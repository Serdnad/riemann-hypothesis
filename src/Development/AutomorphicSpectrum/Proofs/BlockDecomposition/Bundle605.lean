module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle603
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle415
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle392
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle598
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle587
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreePartner

theorem isReduced_tens (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [IsReduced R] : IsReduced (R ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  haveI : Algebra.FormallySmooth F E := inferInstance
  haveI : Algebra.FinitePresentation F E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth F E := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.Smooth R (R ⊗[F] E) := inferInstance
  exact GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R (R ⊗[F] E)

theorem isUnit_det_JR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (h : J.det ≠ 0) :
    IsUnit (JR (F := F) R J).det := by
  have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact (IsUnit.mk0 _ h).map _

theorem exists_partner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hloc x hx
  obtain ⟨-, -, -, -, hA, hRed, -, -⟩ := hloc
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  haveI : IsReduced (R ⊗[F] E) := isReduced_tens F E R
  have hinv : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z :=
    HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hlip := FreeOpen.lip_of_artinian_reduced (R ⊗[F] E)
  obtain ⟨P, hP⟩ := hlip (Fin M) (Fin 1)
    (Matrix.of fun i (_ : Fin 1) => sigR R σ (x i)) (by
      intro c hc
      have h1 : ∀ i, sigR R σ (x i) * c 0 = 0 := by
        intro i
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 : sigR R σ (c 0) • x = 0 := by
        funext i
        have := congrArg (sigR R σ) (h1 i)
        rw [map_mul, hinv, map_zero] at this
        simpa [mul_comm] using this
      have h3 := Fintype.linearIndependent_iff.mp hx (fun _ => sigR R σ (c 0)) (by simpa using h2) 0
      have h4 : c 0 = 0 := by
        have := congrArg (sigR R σ) h3
        simpa [hinv] using this
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h4)
  have hu := isUnit_det_JR (F := F) R hJ.2
  refine ⟨(JR R J)⁻¹ *ᵥ (fun j => P 0 j), ?_⟩
  have hv : JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) = fun j => P 0 j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h00 := congrFun (congrFun hP 0) 0
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq] at h00
  have hform' : hR R σ J x ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) =
      ∑ i, sigR R σ (x i) * (JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j))) i := by
    simp only [hR, hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hform', hv, ← h00]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompanionTheory.WeilSiegel.FreePartner
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.linearly_independent_frames_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (evI realAd At tens Rest IsStd SInf)
open GlobalTheory.WeilM (schr)
open scoped SchwartzMap LineDeriv

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum]


open scoped Classical in
theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add (f := _), map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]

end GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CuspIrred

open scoped InnerProductSpace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem continuous_infGL' : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem map_closure_le {C S : Submodule ℂ (L2 (latticeGL E a) μ)} (hC : C = S.topologicalClosure)
    (T : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) (h : ∀ F ∈ S, T F ∈ C) {v : L2 (latticeGL E a) μ}
    (hv : v ∈ C) : T v ∈ C := by
  have hcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := hC ▸ Submodule.isClosed_topologicalClosure _
  have hle : S.topologicalClosure ≤ C.comap (T : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
    Submodule.topologicalClosure_minimal _ h (hcl.preimage T.continuous)
  exact hle (hC ▸ hv)

theorem R_curve_mem {W : Submodule ℂ (Sm E a)} (hs : _root_.GlobalTheory.CuspRep.IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) {c : ℝ → GL (Fin a) (Cinf E)} {X : GlobalTheory.CuspRep.Lie E a}
    (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) {φ : Sm E a} (hφ : φ ∈ W) (h : MemL2Quotient (latticeGL E a) μ φ.1) (t : ℝ) :
    R (latticeGL E a) μ (infGL E a (c t)) h.toL2 ∈ (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hCcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace C := hCcl.completeSpace_coe
  let ψ : ℕ → Sm E a := fun k => ((lie E a X) ^ k) φ
  have hψ0 : ψ 0 = φ := rfl
  have hψs : ∀ k, ψ (k + 1) = lie E a X (ψ k) := fun k => by
    simp only [ψ, pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, ψ k ∈ W := fun k => by
    induction k with
    | zero => exact hφ
    | succ k ih => rw [hψs]; exact hs (.lie X) _ ih
  have hM : ∀ k, MemL2Quotient (latticeGL E a) μ (ψ k).1 := fun k => (hW _ (hmem k)).2
  have hcont : ∀ k, Continuous (ψ k).1 := fun k => ContAut.continuous_of_isOpen_stab E a _ (hW _ (hmem k)).1.level
  let F : ℕ → ℝ → L2 (latticeGL E a) μ := fun k t => R (latticeGL E a) μ (infGL E a (c t)) (hM k).toL2
  obtain ⟨M, B, hb⟩ := GlobalTheory.T.lie_power_l2_factorial_bound E a μ W hs hW φ hφ X
  have hd : ∀ k t, HasDerivAt (F k) (F (k + 1) t) t := fun k t =>
    GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ (ψ k).1 (ψ (k + 1)).1 (hM k) (hM (k + 1)) (fun t => infGL E a (c t))
      (hcont k) (hcont (k + 1)) (continuous_infGL'.comp hc) (by simp [h0]) (fun s t => by simp [hadd])
      (fun g => by
        have := hasDerivAt_curve (ψ k) g c X h0 hX
        rw [hψs]
        exact this) t
  have hn : ∀ k t, ‖F k t‖ ≤ M * B ^ k * (k.factorial : ℝ) := fun k t => (norm_R _ _).trans_le (hb k (hM k))
  have hF0 : ∀ k, F k 0 ∈ C := fun k => by
    have : F k 0 = (hM k).toL2 := by simp [F, h0]
    rw [this]
    exact Submodule.le_topologicalClosure _ (toL2_mem_classes (hmem k) (hM k))
  have hperp : F 0 t ∈ Cᗮᗮ := (Submodule.mem_orthogonal _ _).2 fun u hu =>
    GlobalTheory.T.analytic_orthogonal_vanishing _ F M B u hd hn (fun k => (Submodule.mem_orthogonal' _ _).1 hu _ (hF0 k)) t
  rw [Submodule.orthogonal_orthogonal] at hperp
  have e : (hM 0).toL2 = h.toL2 := rfl
  exact e ▸ hperp

theorem isSubrep_closure {W : Submodule ℂ (Sm E a)} (hs : _root_.GlobalTheory.CuspRep.IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) :
    IsSubrep (R (latticeGL E a) μ) (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hcls : ∀ F ∈ classes W μ, ∃ φ ∈ W, ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, F = h.toL2 := fun F hF => by
    obtain ⟨φ, hφ, e⟩ := mem_classes.1 hF
    exact ⟨φ, hφ, (hW φ hφ).2, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (hW φ hφ).2.lift_toL2_ae_eq.symm)⟩
  have hfin : ∀ k, ∀ v ∈ C, R (latticeGL E a) μ (finGL E a k) v ∈ C := fun k v hv =>
    map_closure_le hCdef _ (fun F hF => Submodule.le_topologicalClosure _
      (R_mem_classes (fun φ hφ => hs (.fin k) φ hφ) hF)) hv
  let S : Subgroup (GL (Fin a) (Cinf E)) :=
    { carrier := {y | (∀ v ∈ C, R (latticeGL E a) μ (infGL E a y) v ∈ C) ∧
        ∀ v ∈ C, R (latticeGL E a) μ (infGL E a y⁻¹) v ∈ C}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => ⟨fun v hv => by
          rw [map_mul, map_mul]; exact hx.1 _ (hy.1 v hv), fun v hv => by
          rw [_root_.mul_inv_rev, map_mul, map_mul]; exact hy.2 _ (hx.2 v hv)⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩ }
  have hS : S = ⊤ := GlobalTheory.T.subgroup_one_parameter_closed_eq_top E a S fun c X hc h0 hadd hX t => by
    have key : ∀ t, ∀ v ∈ C, R (latticeGL E a) μ (infGL E a (c t)) v ∈ C := fun t v hv =>
      map_closure_le hCdef _ (fun F hF => by
        obtain ⟨φ, hφ, h, rfl⟩ := hcls F hF
        exact R_curve_mem hs hW hc h0 hadd hX hφ h t) hv
    have hinv : (c t)⁻¹ = c (-t) := inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
    exact ⟨key t, by rw [show (c t)⁻¹ = c (-t) from hinv]; exact key (-t)⟩
  refine ⟨Submodule.isClosed_topologicalClosure _, fun g v hv => ?_⟩
  have hy : GeneralLinearGroup.map (pInf E) g ∈ S := hS ▸ Subgroup.mem_top _
  rw [← infGL_mul_finGL g, map_mul]
  exact hy.1 _ (hfin _ v hv)

theorem irred_module : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → W ≠ ⊥ → (∀ φ ∈ W, IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → ∀ φ : Sm E a, (IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → φ ∈ W := by
  rintro E _ _ _ a μ _ _ H hH hi W hs hne hW φ ⟨hφ, -, h, hh⟩
  have hW' : ∀ ψ ∈ W, IsAutForm ψ ∧ MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ hψ =>
    ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2.choose⟩
  have hsub := isSubrep_closure (μ := μ) hs hW'
  have hle : (classes W μ).topologicalClosure ≤ H := by
    refine Submodule.topologicalClosure_minimal _ (fun F hF => ?_) hi.1.1
    obtain ⟨ψ, hψ, e⟩ := mem_classes.1 hF
    obtain ⟨h', hh'⟩ := (hW ψ hψ).2.2
    rwa [show F = h'.toL2 from l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans h'.lift_toL2_ae_eq.symm)]
  have hcl : (classes W μ).topologicalClosure = H := by
    refine (hi.2.2 _ hle hsub).resolve_left fun h0 => ?_
    obtain ⟨ψ, hψ, hψ0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨h', -⟩ := (hW ψ hψ).2.2
    refine toL2_ne_zero h' (ContAut.continuous_of_isOpen_stab E a ψ (hW ψ hψ).1.1.level)
      (fun e => hψ0 (Subtype.ext e)) ?_
    have : h'.toL2 ∈ (classes W μ).topologicalClosure :=
      Submodule.le_topologicalClosure _ (toL2_mem_classes hψ h')
    rw [h0] at this
    exact this
  exact GlobalTheory.T.irreducible_cuspidal_form_l2_mem E a μ H hH hi W hs (fun ψ hψ => ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2⟩) hcl φ hφ.1 h hh

end GlobalTheory.CompanionTheory.CuspIrred
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicHaar

theorem exists_haar_rightInvariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ μ : Measure (GA E a), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a => ⟨Measure.haar, inferInstance, GlobalTheory.CovolGL.isMulRightInvariant E a Measure.haar⟩

end GlobalTheory.CompanionTheory.AdelicHaar
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppCent

theorem comm_of_conj {G : Type} [Group G] (γ p₀ q : G)
    (h : q⁻¹ * (p₀⁻¹ * γ * p₀) * q = p₀⁻¹ * γ * p₀) :
    (p₀ * q * p₀⁻¹) * γ = γ * (p₀ * q * p₀⁻¹) := by
  calc (p₀ * q * p₀⁻¹) * γ = p₀ * q * (p₀⁻¹ * γ * p₀) * p₀⁻¹ := by group
    _ = p₀ * q * (q⁻¹ * (p₀⁻¹ * γ * p₀) * q) * p₀⁻¹ := by rw [h]
    _ = γ * (p₀ * q * p₀⁻¹) := by group

theorem conj_comm {G : Type} [Group G] (γ p₀ t : G) (h : t * γ = γ * t) :
    (p₀⁻¹ * t * p₀)⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * t * p₀) = p₀⁻¹ * γ * p₀ := by
  calc _ = p₀⁻¹ * t⁻¹ * (γ * t) * p₀ := by group
    _ = p₀⁻¹ * t⁻¹ * (t * γ) * p₀ := by rw [h]
    _ = _ := by group

theorem isCompact_closure_zpowers_conj {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (c t : G)
    (h : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (c⁻¹ * t * c) : Set G)) := by
  have hφ : Continuous fun x : G => c⁻¹ * x * c := by fun_prop
  have hK := h.image hφ
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), ?_⟩
  have e : c⁻¹ * t * c = MulAut.conj c⁻¹ t := by simp [MulAut.conj_apply]
  have e' : ∀ x : G, c⁻¹ * x * c = MulAut.conj c⁻¹ x := fun x => by simp [MulAut.conj_apply]
  simp only [e', map_zpow]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, (∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) → ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧ (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔ ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧ cptPart (twCent (MonoidHom.id (UL n w)) γ) = twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ ⟨p1, hp1⟩
  obtain ⟨hW1, hW2, hWc, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hinj : Function.Injective (wexp n l) :=
    (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1.injective
  have huc := GlobalTheory.CompanionTheory.UnitaryContraction.main E hU w hw n b hb ϖ hϖ l hl hyp
  obtain ⟨m, hm, u, hu, hmu⟩ := huc _ hp1
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : UL n w, p₀ = p1 * m := ⟨_, rfl⟩
  have hγ0 : (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
    rw [← hmu]
    congr 1
    rw [hp₀]
    group

  have key : ∀ (q : UL n w) (u' : Fin n → (w.adicCompletion E)ˣ),
      (∀ i, ordL (u' i : w.adicCompletion E) = wexp n l i) →
      (q⁻¹ * (p₀⁻¹ * γ * p₀) * q).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ →
      u = u' ∧ ∃ s : Fin n → (w.adicCompletion E)ˣ,
        q.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * b⁻¹ := by
    intro q u' hu' e
    have e' : q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1 =
        b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ := by
      rw [← hγ0, ← e]
      rfl
    have hh : (b⁻¹ * q.1 * b)⁻¹ * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * (b⁻¹ * q.1 * b) =
        GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' := by
      calc _ = b⁻¹ * (q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1) * b := by
            group
        _ = _ := by rw [e']; group
    obtain ⟨h1, s, hs⟩ := GlobalTheory.CompanionTheory.DiagRigid.diag_rigid (w.adicCompletion E) n (wexp n l) hinj u u'
      hu hu' _ hh
    refine ⟨h1, s, ?_⟩
    rw [← hs]
    group
  refine ⟨p₀, u, hu, hγ0, fun p => ⟨fun hp => ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨m', hm', u', hu', e⟩ := huc _ hp
    have e2 : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = m'⁻¹ * (p⁻¹ * γ * p) * m' := by
      group
    obtain ⟨rfl, -⟩ := key (p₀⁻¹ * p * m') u' hu' (by rw [e2]; exact e)
    have hq : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = p₀⁻¹ * γ * p₀ := by
      apply Subtype.ext
      rw [e2, e, hγ0]
    refine ⟨p₀ * (p₀⁻¹ * p * m') * p₀⁻¹, comm_of_conj γ p₀ _ hq, m'⁻¹, inv_mem hm', ?_⟩
    group
  ·
    rintro ⟨z, hz, i, hi, rfl⟩
    have hz' : z * γ = γ * z := hz
    have e : (z * p₀ * i)⁻¹ * γ * (z * p₀ * i) = i⁻¹ * (p₀⁻¹ * γ * p₀) * i := by
      calc _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (γ * z) * p₀ * i := by group
        _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (z * γ) * p₀ * i := by rw [hz']
        _ = _ := by group
    rw [e, GlobalTheory.CompanionTheory.DiagCoset.fU_diag E hU w hw n b hb ϖ hϖ l hl _ u hu hγ0 _ (inv_mem hi) _ hi]
    exact one_ne_zero
  ·
    refine GlobalTheory.CompanionTheory.CptGen.cptPart_eq_inf (UL n w) _ _ ?_ ?_
    · rw [Subgroup.coe_map]
      refine hWc.image ?_
      change Continuous fun x : UL n w => p₀ * x * p₀⁻¹
      fun_prop
    · intro t ht hc
      have ht' : t * γ = γ * t := ht
      obtain ⟨-, s, hs⟩ := key (p₀⁻¹ * t * p₀) u hu (by rw [conj_comm γ p₀ t ht']; exact hγ0)
      have hv := GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers E w n (UL n w)
        (p₀⁻¹ * t * p₀) b s hs (isCompact_closure_zpowers_conj p₀ t hc)
      have hmem : p₀⁻¹ * t * p₀ ∈ iwU n w b := by
        rw [hW2]
        have : b⁻¹ * (p₀⁻¹ * t * p₀).1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by
          rw [hs]
          group
        rw [this]
        exact GlobalTheory.CompanionTheory.DiagCoset.diagT_mem_iwGL w n s hv
      refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.CompanionTheory.SuppCent
end

section


theorem _root_.GlobalTheory.T.multiplicity_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuLev := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | exact GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev <;> assumption)
end
