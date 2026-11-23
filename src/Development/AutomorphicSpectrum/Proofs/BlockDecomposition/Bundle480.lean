module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorph
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def tupIn {M n : ℕ} (L : Set (R ⊗[F] E)) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∀ i k, X i k ∈ L}

def eMat {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)).updateCol l a

def dMat {n : ℕ} (l : Fin n) (s : R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  Matrix.diagonal (Function.update 1 l s)

def cjM (σ : E →ₐ[F] E) {n : ℕ} (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ * y * g

def nearNF {M n : ℕ} (O L : Set (R ⊗[F] E)) (t : R ⊗[F] E) (j : ℕ) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | X ∈ tupIn R L ∧ ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
    ∀ k, ∑ i, X i k * a i ∈ (fun x => t ^ j * x) '' L}

def goodT {M n : ℕ} (O L : Set (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (j : ℕ) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  tupIn R L \ ⋃ p ∈ S, nearNF R O L (p.1 : R ⊗[F] E) j

def gramIn (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (Y : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ y ∈ Y, gramR R σ J X = (y : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def cjPre (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Y : Set (HermR R σ n)) :
    Set (HermR R σ n) :=
  {y | ∃ z ∈ Y, cjM R σ g (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (z : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

variable [TopologicalSpace R] [MeasurableSpace R]

def IsOrdData (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (O : Subring (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) : Prop :=
  IsCompact (O : Set (R ⊗[F] E)) ∧ IsOpen (O : Set (R ⊗[F] E)) ∧ (∀ x ∈ O, sigR R σ x ∈ O) ∧
  (∀ p ∈ S, (p.1 : R ⊗[F] E) ∈ O ∧ p.2 ≠ 0 ∧ (∀ x, p.2 * x = 0 → (p.1 : R ⊗[F] E) * x = x) ∧
    Filter.Tendsto (fun j : ℕ => p.2 * (p.1 : R ⊗[F] E) ^ j) Filter.atTop (nhds 0) ∧
    ∃ θ : ℝ≥0, θ < 1 ∧ ∀ Y : Set (R ⊗[F] E),
      coordK R b lam ((fun x => (p.1 : R ⊗[F] E) * x) '' Y) = θ * coordK R b lam Y) ∧
  ∀ (n M : ℕ) (X : Fin n → Fin M → R ⊗[F] E), ¬ LinearIndependent (R ⊗[F] E) X →
    ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
      ∀ k, p.2 * ∑ i, X i k * a i = 0

end Alg

section Help

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_mul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) h = rmul R X (g * h) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => mul_assoc _ _ _

theorem hR_sum_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E)
    (y : Fin n → Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J x (fun k => ∑ e, y e k * w e) = ∑ e, hR R σ J x (y e) * w e := by
  simp only [hR, hform, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_sum_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin n → Fin M → R ⊗[F] E)
    (y : Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J (fun k => ∑ c, x c k * w c) y = ∑ c, sigR R σ (w c) * hR R σ J (x c) y := by

  simp only [hR, hform, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cjM R σ g (gramR R σ J X) := by
  ext a c
  change hR R σ J (fun i => ∑ e, X e i * g e a) (fun i => ∑ e, X e i * g e c) = _
  rw [hR_sum_right]
  simp only [hR_sum_left]
  rfl

theorem cjM_mul (σ : E →ₐ[F] E) {n : ℕ} (g h y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ (g * h) y = cjM R σ h (cjM R σ g y) := by
  simp only [cjM, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem cjM_one (σ : E →ₐ[F] E) {n : ℕ} (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ 1 y = y := by
  simp [cjM, Matrix.map_one, map_zero, map_one]

theorem cjM_mem (σ : E →ₐ[F] E) (hσ : ∀ x, sigR R σ (sigR R σ x) = x) {n : ℕ}
    (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hy : y ∈ HermR R σ n) : cjM R σ g y ∈ HermR R σ n := by
  intro a c
  have hy' : ∀ a c, sigR R σ (y c a) = y a c := hy

  simp only [cjM, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, hσ, hy']
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Fin n → R ⊗[F] E :=
  fun i => if i = l then 1 else - a i

theorem eMat_mul_negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) (hl : a l = 1) :
    eMat R l a * eMat R l (negCol R l a) = 1 := by
  ext i k
  simp only [Matrix.mul_apply, eMat, Matrix.updateCol_apply, Matrix.one_apply]
  by_cases hk : k = l
  · subst hk
    simp only [if_true, negCol]
    have : ∀ c, (if c = k then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else - a c) =
        (if c = k then a i else 0) + (if c = i then (if i = k then 0 else - a i) else 0) := by
      intro c
      by_cases h1 : c = k
      · subst h1
        by_cases h2 : c = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : c = i
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : i = k
    · subst h; simp [hl]
    · simp [h]
  · simp only [hk, if_false]
    have : ∀ c, (if c = l then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else 0) =
        if c = k then (if i = k then 1 else 0) else 0 := by
      intro c
      by_cases h1 : c = k
      · subst h1; simp [hk]
      · simp [h1]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem dMat_mul {n : ℕ} (l : Fin n) (s t : R ⊗[F] E) (h : s * t = 1) : dMat R l s * dMat R l t = 1 := by
  rw [dMat, dMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = l
  · subst hi; simpa using h
  · simp [Function.update_of_ne hi]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isCompact_tupIn [TopologicalSpace (R ⊗[F] E)] {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsCompact L) :
    IsCompact (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => L := by
    ext X
    simp [tupIn]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hL

end Help

end GlobalTheory.CompanionTheory.AvgFree
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree

theorem linearIndependent_gl_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K)
    (X : Fin n → Fin M → K) (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem actW_linearIndependent_iff : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) (actW R σ J h X) ↔ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ R _ _ σ M n J h X
  set g := HA.mat R σ J h with hg
  have hact : actW R σ J h X = fun a => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (X a) := rfl
  refine ⟨fun hY => ?_, fun hX => ?_⟩
  · have h2 := linearIndependent_gl_mulVec g⁻¹ _ hY
    have h3 : (fun a => ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec
        (actW R σ J h X a)) = X := by
      funext a
      rw [hact]
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rwa [h3] at h2
  · rw [hact]
    exact linearIndependent_gl_mulVec g X hX

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.unit_scaling_rank_one_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  first | exact @GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul | exact GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul | (intros; apply GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.local_dependent_set_null : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → coordW (Fv F v) b lam 1 M {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree.null_nonfree | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree.null_nonfree | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree.null_nonfree <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.hermitian_block_decomposition_homeomorph : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∃ e : HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), (∀ S, ((e S).1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 ∧ (∀ j : Fin n, (e S).2.1 0 j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) ∧ ∀ i j : Fin n, ((e S).2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) ∧ MeasurePreserving e (coordHerm R σ b lam (n + 1)) ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit <;> assumption)
end

section

noncomputable section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology

namespace GlobalTheory.CompanionTheory.CTFin.Central

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_mul {r : ℕ} {φ : Sm E a} (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set f₀ := JointCont.finPart g x₀
  have hc : Continuous (fun x : BlockIx a r → Ad E => f₀⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a (f₀⁻¹ * f₀) φ = φ := by rw [inv_mul_cancel]; simp
  have hev : ∀ᶠ x in 𝓝 x₀, chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val) = φ.1 (unip x * g) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.mem_nhds h1)] with x hx
    have hx' : finRep E a (f₀⁻¹ * JointCont.finPart g x) φ = φ := hx
    have e : unip x * g = finGL E a f₀ * infGL E a (JointCont.infPart g x) * finGL E a (f₀⁻¹ * JointCont.finPart g x) := by
      rw [JointCont.unip_mul_eq, mul_assoc, infGL_comm, ← mul_assoc, ← map_mul (finGL E a), mul_inv_cancel_left]
    rw [chart_val, e]
    exact (congrArg (fun ψ : Sm E a => ψ.1 (finGL E a f₀ * infGL E a (JointCont.infPart g x))) hx').symm
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E => chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a f₀))
      ((φ.2 _).continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  exact hA.congr hev

theorem exists_bound_unip_mul {r : ℕ} {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_unip_mul (r := r) hφ g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hper : φ.1 (unip x * g) = φ.1 (unip (fun p => x p - algebraMap E (Ad E) (q p)) * g) := by
    conv_lhs => rw [hx]
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hper]
  exact hC _ fun p _ => hq p

theorem integrable_unip_mul {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) (μ.restrict 𝓕) := by
  have hfin := covol_lt_top μ 𝓕 h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) hl hφ g
  exact Integrable.of_bound (continuous_unip_mul hφ g).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem ct_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 hlie
  haveI := hμ
  let P : Sm E a → Prop := fun φ =>
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}
  have hadd : ∀ φ ψ : Sm E a, P φ → P ψ → P (φ + ψ) := fun φ ψ h1 h2 =>
    ⟨fun γ g => by
      change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
      rw [h1.1, h2.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).add_mem (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)
       (show ψ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h2.2)⟩
  have hsmul : ∀ (c : ℂ) (φ : Sm E a), P φ → P (c • φ) := fun c φ h1 =>
    ⟨fun γ g => by
      change c • φ.1 _ = c • φ.1 _
      rw [h1.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).smul_mem c (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)⟩
  have hint : ∀ ψ : Sm E a, P ψ → ∀ g, Integrable (fun x => ψ.1 (unip x * g)) (μ.restrict 𝓕) :=
    fun ψ h g => integrable_unip_mul μ 𝓕 h𝓕 h.1 h.2 g
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {T | ∀ φ, P φ → P (T φ) ∧ ∀ F : Sm E a, (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
          ∀ g, (T F).1 g = ∫ x in 𝓕, (T φ).1 (unip x * g) ∂μ}
      mul_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₂ φ hφ
        obtain ⟨h2, e2⟩ := hT₁ _ h1
        exact ⟨h2, fun F hF g => e2 (T₂ F) (e1 F hF) g⟩
      add_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₁ φ hφ
        obtain ⟨h2, e2⟩ := hT₂ φ hφ
        refine ⟨hadd _ _ h1 h2, fun F hF g => ?_⟩
        change (T₁ F).1 g + (T₂ F).1 g = ∫ x in 𝓕, ((T₁ φ).1 (unip x * g) + (T₂ φ).1 (unip x * g)) ∂μ
        rw [integral_add (hint _ h1 g) (hint _ h2 g), e1 F hF g, e2 F hF g]
      algebraMap_mem' := fun c φ hφ => by
        refine ⟨by rw [Module.algebraMap_end_apply]; exact hsmul c φ hφ, fun F hF g => ?_⟩
        rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        change c • F.1 g = ∫ x in 𝓕, c • φ.1 (unip x * g) ∂μ
        rw [integral_smul, hF g] }
  have hL : ∀ X, lie E a X ∈ S := fun X φ hφ =>
    ⟨⟨fun γ g => GlobalTheory.SpehInfChar.lie_leftInv (ratGL E a).range X
        (fun u hu g' => by obtain ⟨γ', rfl⟩ := MonoidHom.mem_range.1 hu; exact hφ.1 γ' g') _ ⟨γ, rfl⟩ g,
      GlobalTheory.SpehInfChar.lie_mem_smoothPart X (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from hφ.2)⟩,
     fun F hF g => hlie φ F hφ.1 hφ.2 hF X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  intro φ F hl hlev hF z hz g
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, hlev⟩).2 F hF g

end GlobalTheory.CompanionTheory.CTFin.Central
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.Growth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem exists_unip_bound {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : BlockIx a r → Ad E) (y : GL (Fin a) (Cinf E)),
      ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hT : IsCompact ((fun x => JointCont.finPart g x) '' Cm) :=
    hCm.image (JointCont.continuous_finPart g)
  obtain ⟨C₀, N, hC₀, hgrow⟩ := GlobalTheory.CompanionTheory.BoxBound.exists_growth_uniform hφ hT
  have hI : Continuous (fun x : BlockIx a r → Ad E => JointCont.infPart g x) := by
    have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
      continuous_pi fun p => JointCont.continuous_pInf.comp (continuous_apply p)
    exact (JointCont.continuous_unip.comp h1).mul continuous_const
  obtain ⟨B, hB⟩ := (hCm.image (GlobalTheory.CompanionTheory.BoxBound.continuous_height.comp hI)).bddAbove
  have hc : (0 : ℝ) ≤ 1 + 2 * a := by positivity
  refine ⟨C₀ * ((1 + 2 * a) * max B 1) ^ N, N, by positivity, fun x y => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Cm, x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  have e1 : unip ((fun p => algebraMap E (Ad E) (q p)) + x') * (g * infGL E a y) =
      ratGL E a (unip q) * (finGL E a (JointCont.finPart g x') * infGL E a (JointCont.infPart g x' * y)) := by
    rw [unip_add, unip_algebraMap, mul_assoc, ← mul_assoc (unip x'), JointCont.unip_mul_eq, map_mul, mul_assoc]
  rw [e1, hφ.left]
  refine (hgrow _ ⟨x', hx'm, rfl⟩ _).trans ?_
  have hb : height (JointCont.infPart g x') ≤ max B 1 := le_trans (hB ⟨x', hx'm, rfl⟩) (le_max_left _ _)
  have hy := one_le_height y
  have hH : height (JointCont.infPart g x' * y) ≤ (1 + 2 * a) * max B 1 * height y := by
    refine (GlobalTheory.CompanionTheory.BoxBound.height_mul_le' _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by linarith)) hc
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [one_le_height (JointCont.infPart g x' * y)]) hH N) hC₀

theorem ct_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r φ hφ _ _ μ 𝓕 hμ hF g
  have := hμ
  obtain ⟨C, N, -, h⟩ := exists_unip_bound (r := r) hφ g
  refine ⟨C * μ.real 𝓕, N, fun y => ?_⟩
  refine (norm_setIntegral_le_of_norm_le_const (covol_lt_top μ 𝓕 hF) fun x _ => h x y).trans_eq ?_
  ring

end GlobalTheory.CompanionTheory.CTFin.Growth

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.finite_dim_stable_subspace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (W : Submodule ℂ (Sm E a)), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → ∀ φ ∈ W, ∃ Y : Submodule ℂ (Sm E a), FiniteDimensional ℂ Y ∧ Y ≤ W ∧ φ ∈ Y ∧ (∀ z ∈ Zalg E a, ∀ y ∈ Y, z y ∈ Y) ∧ ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ y ∈ Y, lie E a X y ∈ Y := by
  first | exact @GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable | exact GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable | (intros; apply GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable <;> assumption)
end
