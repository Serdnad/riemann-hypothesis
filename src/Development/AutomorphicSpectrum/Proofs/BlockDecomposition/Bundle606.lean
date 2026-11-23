module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle909
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle598
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.StableMod

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isCuspForm_fin (k : GL (Fin a) (Af E)) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (finRep E a k φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
    rw [mul_assoc, hA.left]
  · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
        (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
      ext k'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · intro e
        rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply]
      · intro e
        have := congrArg (finRep E a k) e
        rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_apply] at this
    change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
    rw [e]
    exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
      (finRep E a k)) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
  · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
    rw [mul_assoc, infGL_comm, ← mul_assoc]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)

theorem isCuspForm_cpt (c : Kinf E a) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (cptRep E a c φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
    rw [mul_assoc, hA.left]
  · exact level_of_le hA.level fun k hk => by
      change finRep E a k (cptRep E a c φ) = cptRep E a c φ
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨c', rfl⟩
    refine Submodule.subset_span ⟨c' * c, ?_⟩
    change _ = (cptRep E a c' * cptRep E a c) φ
    rw [← map_mul]
  · exact zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_compactRep E a c z hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := growth_mul (Unitary.toUnits c) (hA.growth g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
    rw [mul_assoc, ← map_mul]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))

theorem lieD_left {φ : Sm E a} (X : Lie E a) {u : GA E a} (hu : ∀ g, φ.1 (u * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (u * g) = (lie E a X φ).1 g := by
  change lieD X φ.1 (u * g) = lieD X φ.1 g
  have e : chart φ.1 (u * g) = chart φ.1 g := by
    funext x
    unfold chart
    split_ifs
    · rw [mul_assoc, hu]
    · rfl
  unfold lieD
  rw [e]

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (H : Submodule ℂ (L2 (latticeGL E a) μ))

def formSpace (hH : IsSubrep (R (latticeGL E a) μ) H) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
    ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H}
  zero_mem' := by
    refine ⟨⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩, fun _ _ => rfl, ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (0 : Sm E a).1 := ⟨fun _ _ _ => rfl, MemLp.zero⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = 0 := MemLp.toLp_zero _
    rw [this]
    exact zero_mem _
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h5, h6, h7, h8⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a 1 φ ψ h1 h5
    rw [one_smul] at e
    refine ⟨e, fun t g => ?_, ?_⟩
    · exact congrArg₂ (· + ·) (h2 t g) (h6 t g)
    · have h : MemL2Quotient (latticeGL E a) μ (φ + ψ).1 := ⟨fun γ hγ g => congrArg₂ (· + ·) (h3.1 γ hγ g) (h7.1 γ hγ g), h3.2.add h7.2⟩
      refine ⟨h, ?_⟩
      have : h.toL2 = h3.toL2 + h7.toL2 := MemLp.toLp_add h3.2 h7.2
      rw [this]
      exact add_mem h4 h8
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    have hz : IsCuspForm (0 : Sm E a) :=
      ⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a c φ 0 h1 hz
    rw [add_zero] at e
    refine ⟨e, fun t g => congrArg (c • ·) (h2 t g), ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (c • φ).1 := ⟨fun γ hγ g => congrArg (c • ·) (h3.1 γ hγ g), h3.2.const_smul c⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = c • h3.toL2 := MemLp.toLp_const_smul c h3.2
    rw [this]
    exact H.smul_mem c h4


open GroundTheory.Automorphic in
theorem exists_stable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)) (_ : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) :
    ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ _root_.GlobalTheory.CuspRep.IsStable V := by
  have hS : IsSubrep (R (latticeGL E a) μ) H := hi.1
  refine ⟨formSpace μ H hS, fun φ => Iff.rfl, ?_⟩
  rintro o φ ⟨h1, h2, h3, h4⟩
  cases o with
  | fin k =>
    refine ⟨isCuspForm_fin k h1, fun t g => ?_, h3.mul_right (finGL E a k), ?_⟩
    · change φ.1 (splitCentre E a t * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | cpt k =>
    refine ⟨isCuspForm_cpt k h1, fun t g => ?_, h3.mul_right (infGL E a (Unitary.toUnits k)), ?_⟩
    · change φ.1 (splitCentre E a t * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | lie X =>
    letI : MeasurableSpace (AutomorphicForm.archGroup E a) := borel _
    haveI : BorelSpace (AutomorphicForm.archGroup E a) := ⟨rfl⟩
    obtain ⟨D, hD, hDc, hrep⟩ := GlobalTheory.T.lie_derivative_convolution_kernel E a (Measure.haar : Measure (AutomorphicForm.archGroup E a)) φ h1.1 X
    have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h1.1.level
    obtain ⟨h', hW⟩ := GlobalTheory.T.l2_convolution_locally_compact_mem (latticeGL E a) μ (Measure.haar : Measure (AutomorphicForm.archGroup E a))
      (AutomorphicForm.infEmb E a) AutomorphicForm.continuous_infEmb D hD hDc φ.1 (lie E a X φ).1 hc h3 hrep
    refine ⟨⟨⟨fun γ g => lieD_left X (h1.1.left γ) g, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ h1.1.kfin,
      GlobalTheory.CuspStab.zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_lie_action E a X z hz) h1.1.zfin,
      GlobalTheory.T.moderate_growth_convolution_integral E a _ φ.1 _ hc h1.1.growth D hD hDc hrep⟩, GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm E a X φ h1⟩,
      fun t g => lieD_left X (h2 t) g, h', hW H hS h4⟩
    exact GlobalTheory.CuspStab.level_of_le h1.1.level fun k hk => by
      change finRep E a k (lie E a X φ) = lie E a X φ
      change (rt E a (finGL E a k) * lie E a X) φ = _
      rw [← lie_rt_fin, Module.End.mul_apply]
      exact congrArg (lie E a X) hk

end GlobalTheory.CompanionTheory.StableMod
end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.S2.Clozel Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.PeterssonSkew

theorem integral_deriv_eq_zero {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (u v u' v' : ℝ → Q → ℂ) (C : ℝ)
    (hu : ∀ t q, HasDerivAt (fun s => u s q) (u' t q) t) (hv : ∀ t q, HasDerivAt (fun s => v s q) (v' t q) t)
    (bu : ∀ t q, ‖u t q‖ ≤ C) (bv : ∀ t q, ‖v t q‖ ≤ C) (bu' : ∀ t q, ‖u' t q‖ ≤ C) (bv' : ∀ t q, ‖v' t q‖ ≤ C)
    (mu : ∀ t, AEStronglyMeasurable (u t) ν) (mv : ∀ t, AEStronglyMeasurable (v t) ν)
    (mu' : AEStronglyMeasurable (u' 0) ν) (mv' : AEStronglyMeasurable (v' 0) ν)
    (hc : ∀ t, ∫ q, u t q * conj (v t q) ∂ν = ∫ q, u 0 q * conj (v 0 q) ∂ν) :
    ∫ q, (u' 0 q * conj (v 0 q) + u 0 q * conj (v' 0 q)) ∂ν = 0 := by
  have mc : ∀ {f : Q → ℂ}, AEStronglyMeasurable f ν → AEStronglyMeasurable (fun q => conj (f q)) ν :=
    fun h => Complex.continuous_conj.comp_aestronglyMeasurable h
  have hC : 0 ≤ C ∨ IsEmpty Q := by
    by_cases h : Nonempty Q
    · obtain ⟨q⟩ := h
      exact Or.inl ((norm_nonneg _).trans (bu 0 q))
    · exact Or.inr (not_nonempty_iff.1 h)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t q => u t q * conj (v t q))
    (F' := fun t q => u' t q * conj (v t q) + u t q * conj (v' t q))
    (bound := fun _ => C * C + C * C) Filter.univ_mem
    (Eventually.of_forall fun t => (mu t).mul (mc (mv t)))
    (Integrable.of_bound ((mu 0).mul (mc (mv 0))) (C * C) (Eventually.of_forall fun q => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (bu 0 q) (bv 0 q) (norm_nonneg _) ((norm_nonneg _).trans (bu 0 q))))
    ((mu'.mul (mc (mv 0))).add ((mu 0).mul (mc mv')))
    (Eventually.of_forall fun q t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul, RCLike.norm_conj]
      · exact mul_le_mul (bu' t q) (bv t q) (norm_nonneg _) ((norm_nonneg _).trans (bu' t q))
      · exact mul_le_mul (bu t q) (bv' t q) (norm_nonneg _) ((norm_nonneg _).trans (bu t q)))
    (integrable_const _)
    (Eventually.of_forall fun q t _ => (hu t q).mul (hv t q).star)
  have h0 : HasDerivAt (fun t : ℝ => ∫ q, u t q * conj (v t q) ∂ν) 0 0 := by
    simp only [hc]
    exact hasDerivAt_const _ _
  exact key.2.unique h0

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open scoped Matrix.Norms.Operator in
theorem exists_curve (X : Lie E a) : ∃ c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E), c 0 = 1 ∧
    (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 := by
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X with hY
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hadd : ∀ s t : ℝ, NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y) := fun s t => by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl Y).smul_left s).smul_right t)
  have hone : ∀ t : ℝ, NormedSpace.exp (t • Y) * NormedSpace.exp ((-t) • Y) = 1 := fun t => by
    rw [← hadd, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), NormedSpace.exp ((-t) • Y), hone t, by simpa using hone (-t)⟩,
    Units.ext (by simp [NormedSpace.exp_zero]), fun s t => Units.ext (hadd s t), ?_⟩
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_translate {X : Lie E a} {c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E)} (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hX : HasDerivAt (fun t => toL (c t).val) X 0) (φ : Sm E a) (g : GA E a)
    (t : ℝ) : HasDerivAt (fun s => φ.1 (g * infGL E a (c s))) (lieD X φ.1 (g * infGL E a (c t))) t := by
  have h := hasDerivAt_curve φ (g * infGL E a (c t)) c X h0 hX
  have h2 : HasDerivAt (fun s => φ.1 (g * infGL E a (c t) * infGL E a (c (s - t))))
      (lieD X φ.1 (g * infGL E a (c t))) t := HasDerivAt.comp_sub_const t t (by simpa using h)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [mul_assoc, ← map_mul, ← hadd]
  simp

theorem pet_mul_right (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ ψ : GA E a → ℂ}
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ) (g : GA E a) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ ψ := by
  rw [← MemL2Quotient.inner_toL2_eq_theta_pairing (hφ.mul_right g) (hψ.mul_right g), ← right_translate_toL2, ← right_translate_toL2, ← MemL2Quotient.inner_toL2_eq_theta_pairing hφ hψ]
  exact LinearIsometry.inner_map_map
    { toLinearMap := (R (GlobalTheory.UnitaryBC.latticeGL E a) μ g :
        L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ →L[ℂ] L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ).toLinearMap
      norm_map' := norm_R g } _ _

theorem pet_lie_add (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E a) (φ ψ : Sm E a)
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1)
    (hφ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1)
    (hψ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X ψ).1)
    (C : ℝ) (bφ : ∀ g, ‖φ.1 g‖ ≤ C) (bψ : ∀ g, ‖ψ.1 g‖ ≤ C)
    (bφ' : ∀ g, ‖(lie E a X φ).1 g‖ ≤ C) (bψ' : ∀ g, ‖(lie E a X ψ).1 g‖ ≤ C) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1 ψ.1 +
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 (lie E a X ψ).1 = 0 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨c, h0, hadd, hX⟩ := exists_curve X
  have e0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have key := integral_deriv_eq_zero (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GlobalTheory.UnitaryBC.latticeGL E a) μ)
    (fun t q => φ.1 (q.out * infGL E a (c t))) (fun t q => ψ.1 (q.out * infGL E a (c t)))
    (fun t q => lieD X φ.1 (q.out * infGL E a (c t))) (fun t q => lieD X ψ.1 (q.out * infGL E a (c t))) C
    (fun t q => hasDerivAt_translate h0 hadd hX φ q.out t) (fun t q => hasDerivAt_translate h0 hadd hX ψ q.out t)
    (fun _ _ => bφ _) (fun _ _ => bψ _) (fun _ _ => bφ' _) (fun _ _ => bψ' _)
    (fun t => (hφ.mul_right (infGL E a (c t))).2.aestronglyMeasurable) (fun t => (hψ.mul_right (infGL E a (c t))).2.aestronglyMeasurable)
    (by simp only [e0, mul_one]; exact hφ'.2.aestronglyMeasurable) (by simp only [e0, mul_one]; exact hψ'.2.aestronglyMeasurable)
    (fun t => by
      have h1 := pet_mul_right μ hφ hψ (infGL E a (c t))
      simp only [e0, mul_one]
      exact h1)
  simp only [e0, mul_one] at key
  exact (integral_add (hφ'.integrable_mul_conj hψ) (hφ.integrable_mul_conj hψ')).symm.trans key

theorem lie_skew_adjoint : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a) (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1), (∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) → ∀ (X : Lie E a) (φ ψ : π.V), inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm ψ) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) φ)) = -inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) ψ)) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm φ) := by
  intro E _ _ _ a μ _ _ π hm hb X φ ψ
  have hL : ∀ f : π.V, ∃ C : ℝ, ∀ g, ‖f.1.1 g‖ ≤ C := fun f => hb f.1 f.2
  obtain ⟨C₁, b₁⟩ := hL φ
  obtain ⟨C₂, b₂⟩ := hL ψ
  obtain ⟨C₃, b₃⟩ := hL (π.op (.lie X) φ)
  obtain ⟨C₄, b₄⟩ := hL (π.op (.lie X) ψ)
  have h := pet_lie_add μ X φ.1 ψ.1 (hm _ φ.2) (hm _ ψ.2) (hm _ (π.op (.lie X) φ).2) (hm _ (π.op (.lie X) ψ).2)
    (max (max C₁ C₂) (max C₃ C₄))
    (fun g => (b₁ g).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun g => (b₂ g).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (fun g => (b₃ g).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun g => (b₄ g).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have e1 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ (π.op (.lie X) φ).2) (hm _ ψ.2)
  have e2 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ φ.2) (hm _ (π.op (.lie X) ψ).2)
  change inner ℂ (hm _ ψ.2).toL2 (hm _ (π.op (.lie X) φ).2).toL2 =
    -inner ℂ (hm _ (π.op (.lie X) ψ).2).toL2 (hm _ φ.2).toL2
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left h

end GlobalTheory.CompanionTheory.PeterssonSkew
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.block_det_order_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ordL (blk h w m X).val.det = ordL m.1.val.det + ordL m.2.val.det := by
  first | exact @GlobalTheory.CompanionTheory.CtS.ordL_blk_det | exact GlobalTheory.CompanionTheory.CtS.ordL_blk_det | (intros; apply GlobalTheory.CompanionTheory.CtS.ordL_blk_det <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.unramified_character_block_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (c : ℂˣ) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) = (c : ℂ) ^ (i * b + j * a) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist | exact GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist | (intros; apply GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

theorem ordL_pow_div_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (a b : ℕ) :
    ordL (x ^ b / y ^ a) = (b : ℤ) * ordL x - (a : ℤ) * ordL y := by
  have h : x ^ b / y ^ a =
      (((Units.mk0 x hx) ^ (b : ℤ) * (Units.mk0 y hy) ^ (-(a : ℤ)) : Lˣ) : L) := by
    simp [div_eq_mul_inv]
  rw [h, Units.val_mul, GlobalTheory.CompanionTheory.SwapInt.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
    GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow]
  simp only [Units.val_mk0]
  ring

theorem absHalf_blockDet_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (qV E w : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) := by
  intro E _ _ _ a b w i j m hi hj
  have h1 : m.1.val.det ≠ 0 := by
    have := m.1.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h2 : m.2.val.det ≠ 0 := by
    have := m.2.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hq : 0 < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have ho := ordL_pow_div_pow h1 h2 a b
  rw [hi, hj] at ho
  unfold absHalf
  rw [ho]
  have hs : Real.sqrt ((qV E w : ℝ) ^ (-((b : ℤ) * (i : ℤ) - (a : ℤ) * (j : ℤ)))) =
      (qV E w : ℝ) ^ (-((i : ℝ) * b - (j : ℝ) * a) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast
    ring
  rw [hs, Complex.ofReal_cpow hq.le, Complex.ofReal_natCast]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.CtS
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section
namespace GlobalTheory.CompanionTheory.FinSign

theorem ordL_eq_zero_of_v_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (h : Valued.v x = 1) : ordL x = 0 := by
  unfold ordL
  rw [dite_eq_right (by rw [h]; exact one_ne_zero)]
  simp [h]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  intro E _ _ _ hU n γ₀ H₀ _ _ hpos P₁
  obtain ⟨hd0, -⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine (GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 _ hd0)).subset ?_
  rintro w ⟨hw, hs⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0]
  intro h1
  apply hs
  unfold sgnOn
  have hv : Valued.v (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H₀
        (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))).det) = 1 :=
    (w.valuedAdicCompletion_eq_valuation' _).trans h1
  rw [aeval_map_mat, GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq E hU w hw n H₀ (aeval γ₀.val P₁), ordL_eq_zero_of_v_eq_one hv]
  simp

end GlobalTheory.CompanionTheory.FinSign
end
end
