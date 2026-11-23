module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle358
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle369
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle395
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthConv

open GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def rmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := rmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    mul_add (Matrix.of z) (Matrix.of x) (Matrix.of y)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.mul_smul (Matrix.of z) c (Matrix.of x)

def lmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

theorem continuous_rmul : Continuous (rmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (rmulLin (E := E) (a := a)).continuous_of_finiteDimensional

theorem continuous_lmul : Continuous (lmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (lmulLin (E := E) (a := a)).continuous_of_finiteDimensional

def bnd (c : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖

theorem height_mul_le_bnd (c y : GL (Fin a) (Cinf E)) : height (y * c) ≤ bnd c * height y := by
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height bnd
  rw [h1, h2]
  nlinarith

theorem toGL_inv (u : AutomorphicForm.archGroup E a) : toGL E a u⁻¹ = (toGL E a u)⁻¹ := by
  simp only [toGL, map_inv]

theorem continuous_bnd : Continuous fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u) := by
  have hm : Continuous (mMap E a) := (mMap E a).continuous_of_finiteDimensional
  have hv : Continuous fun u : AutomorphicForm.archGroup E a =>
      ((u : (AutomorphicForm.ArchMatrix E a)ˣ) : AutomorphicForm.ArchMatrix E a) :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun u : AutomorphicForm.archGroup E a => toL (toGL E a u).val := by
    simp_rw [toL_toGL]
    exact hm.comp hv
  have h2 : Continuous fun u : AutomorphicForm.archGroup E a => toL ((toGL E a u)⁻¹).val := by
    simp_rw [← toGL_inv, toL_toGL]
    exact hm.comp (hv.comp continuous_inv)
  unfold bnd
  exact (continuous_const.add (continuous_rmul.comp h1).norm).add (continuous_lmul.comp h2).norm

theorem growth_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a _ _ ν _ φ ψ _ hgrow D hD hDc hψ g
  obtain ⟨C, N, hC⟩ := hgrow g
  have hpos : ∀ y : GL (Fin a) (Cinf E), 0 ≤ height y := fun y => by
    linarith [one_le_height y]
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (f := fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u))
    hDc continuous_bnd.continuousOn
  have hint : Integrable (fun u => ‖D u‖) ν := (hD.integrable_of_hasCompactSupport hDc).norm
  refine ⟨C * B ^ N * ∫ u, ‖D u‖ ∂ν, N, fun y => ?_⟩
  have pt : ∀ u, ‖φ (g * infGL E a y * AutomorphicForm.infEmb E a u) * D u‖ ≤
      (C * (B * height y) ^ N) * ‖D u‖ := fun u => by
    by_cases hu : u ∈ tsupport D
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have e : g * infGL E a y * AutomorphicForm.infEmb E a u = g * infGL E a (y * toGL E a u) := by
        rw [infEmb_eq, mul_assoc, map_mul]
      rw [e]
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _) ?_ N) C0)
      exact (height_mul_le_bnd _ y).trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB u hu)) (hpos y))
    · rw [image_eq_zero_of_notMem_tsupport hu]
      simp
  have key := norm_integral_le_of_norm_le (hint.const_mul (C * (B * height y) ^ N)) (Filter.Eventually.of_forall pt)
  rw [hψ]
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, mul_pow]
  ring

end GlobalTheory.CompanionTheory.GrowthConv
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.LieConv

theorem mMap_surjective (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Function.Surjective (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a) := fun X =>
  ⟨(fun i j => ((0, fun w => X i j w.1) : mixedEmbedding.mixedSpace E) :
    Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), rfl⟩

theorem exists_kernel_basis (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ)
    (j : Fin (CuspidalSpectrum.archDim E a)) :
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a,
      (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (CuspidalSpectrum.archBasis E a j)) φ).1 g =
        ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  obtain ⟨D, hD, hDc, h⟩ := GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ) hφ ν 1
    (fun _ => j)
  refine ⟨D, hD, hDc, fun g => ?_⟩
  rw [← h g, CuspidalSpectrum.uAction_uJ_succ]
  have e := GlobalTheory.CompanionTheory.HCRep.smL_liB (E := E) (a := a) (CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis E a j)) φ
  have e2 := congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1 g) e
  have e0 : ∀ ψ : AutomorphicForm.archSmooth E a,
      AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) 0 (Fin.tail fun _ => j)) ψ = ψ := fun ψ => by
    rw [CuspidalSpectrum.uJ, map_one]
    rfl
  rw [e0]
  exact e2

theorem hasCompactSupport_sum {G ι : Type*} [TopologicalSpace G] (s : Finset ι) (c : ι → ℂ) (D : ι → G → ℂ)
    (h : ∀ j, HasCompactSupport (D j)) : HasCompactSupport fun y => ∑ j ∈ s, c j * D j y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((h j).mul_left (f := fun _ => c j)).add ih

theorem lie_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  intro E _ _ _ a _ _ ν _ φ hφ X
  obtain ⟨Y, rfl⟩ := mMap_surjective E a X
  choose D hD hDc hconv using exists_kernel_basis E a ν φ hφ
  set b := CuspidalSpectrum.archBasis E a with hb
  set c : Fin (CuspidalSpectrum.archDim E a) → ℂ := fun j => ((b.repr Y j : ℝ) : ℂ) with hc
  refine ⟨fun y => ∑ j, c j * D j y, continuous_finsetSum _ fun j _ => continuous_const.mul (hD j),
    hasCompactSupport_sum _ c D hDc, fun g => ?_⟩
  have hf : Continuous fun y => φ.1 (g * AutomorphicForm.infEmb E a y) :=
    IsExpLieAlgebra.continuous_of_isSmoothFun (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ g)
  have hint : ∀ j, Integrable (fun y => φ.1 (g * AutomorphicForm.infEmb E a y) * D j y) ν := fun j =>
    (hf.mul (hD j)).integrable_of_hasCompactSupport ((hDc j).mul_left)
  have hY : (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a Y) φ).1 g =
      ∑ j, c j * (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (b j)) φ).1 g := by
    conv_lhs => rw [← b.sum_repr Y]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
    Complex.real_smul, hc]
  rw [hY]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconv j g, ← integral_const_mul]
    congr 1
    funext y
    ring
  · exact ((hint j).const_mul (c j)).congr (Filter.Eventually.of_forall fun y => by ring)

end GlobalTheory.CompanionTheory.LieConv
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.MemC
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cocompact (i t : ℕ) : ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧
    ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := GlobalTheory.T.mirabolic_compact_mod_parabolic k i t

theorem smooth_eC {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) :
    IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := GlobalTheory.T.isOpen_right_invariance_local_coefficient k i t ψ τ σ f

theorem conj_data {i t : ℕ} (h : MirabolicParabolic k (i + 1) t) :
    ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧
      pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1,
        (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := GlobalTheory.T.parabolic_proj_shifted_embedding k i t h

theorem conj_d {i t : ℕ} (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k) :
    ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧
      dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) =
        sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) *
          dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := GlobalTheory.T.unipotent_commute_shifted_embedding k i t h d

theorem qC_sigX_unip {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1))
    (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1)
    (w : τ.V ⊗[ℂ] σ.V) : qC τ σ (sigX τ σ u w) = qC τ σ w := GlobalTheory.T.coinvariant_unipotent_action_trivial k i t τ σ u h1 h2 w

theorem qC_sigX_levi {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1))
    (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1,
        (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V) :
    qC τ σ (sigX τ σ η w) =
      ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 *
        dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) •
      sigC τ σ h (qC τ σ w) := GlobalTheory.T.coinvariant_levi_action_modulus k i t τ σ h η hη w

theorem dpowM_hgp {i t : ℕ} (s : ℝ) (h : MirabolicParabolic k (i + 1) t) :
    dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) =
      dpow (i + 1) s (gpProj k (i + 1) t h).1 *
        dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := GlobalTheory.T.modulus_mirabolic_block_factor k i t s h

theorem smInt_scale {t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W)
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) =
      ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k t) φ := GlobalTheory.T.integral_linear_change_modulus k t W A φ l c

theorem integrand_lc {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}
    (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧
    HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := GlobalTheory.T.local_constancy_twisted_translate k i t ψ hψ τ σ f y

theorem dpow_add (n : ℕ) (a b : ℝ) (g : GL (Fin n) k) : dpow n (a + b) g = dpow n a g * dpow n b g := by
  unfold dpow
  rw [Complex.ofReal_add, absPow_add]
  rfl

theorem dpow_zero (n : ℕ) (g : GL (Fin n) k) : dpow n 0 g = 1 := by
  unfold dpow
  rw [Complex.ofReal_zero, absPow_zero]
  rfl

theorem isFinite_muD (t : ℕ) : @MeasureTheory.IsFiniteMeasureOnCompacts (Fin t → k) (_root_.borel _) _ (muD k t) := by
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem eval_mul {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (h : HPG k (i + 1) (t + 1))
    (x : Mir k ((i + 1) + (t + 1))) : evX f ((h : Mir k ((i + 1) + (t + 1))) * x) = sigX τ σ h (evX f x) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 h x

theorem pointwise {i t : ℕ} (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (h : MirabolicParabolic k (i + 1) t) (y : Mir k ((i + 1) + t + 1)) (d : Fin (t + 1) → k) :
    qC τ σ (evX f (dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * y)) =
      ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 *
        dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) •
      sigC τ σ h (qC τ σ (evX f (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y))) := by
  obtain ⟨η, hη1, hη2⟩ := conj_data h
  obtain ⟨u, hu1, hu2, hu3⟩ := conj_d h d
  rw [hu3, ← hη1, mul_assoc, mul_assoc]
  have e1 := eval_mul f η ((u : Mir k ((i + 1) + t + 1)) * (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y))
  have e2 := eval_mul f u (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y)
  refine (congrArg (qC τ σ) e1).trans ?_
  rw [qC_sigX_levi τ σ h η hη2]
  refine congrArg _ (congrArg _ ?_)
  refine (congrArg (qC τ σ) e2).trans ?_
  exact qC_sigX_unip τ σ u hu1 hu2 _

theorem last_inv {t : ℕ} (p : Mir k t) (d : Fin (t + 1) → k) :
    (((p : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) (Fin.last t) = d (Fin.last t) :=
  mulVec_last_of_mem k _ (inv_mem p.2) d

theorem scalar_one {i t : ℕ} (g : GL (Fin (i + 1)) k) (A : GL (Fin (t + 1)) k) :
    (dpow (i + 1) (-1 / 2) g * dpow (t + 1) (-1 / 2) A) * (dpow (t + 1) 1 A * (dpow (i + 1) (1 / 2) g * dpow (t + 1) (-1 / 2) A)) = 1 := by
  have h1 : dpow (i + 1) (-1 / 2) g * dpow (i + 1) (1 / 2) g = 1 := by
    rw [← dpow_add, show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, dpow_zero]
  have h2 : dpow (t + 1) (-1 / 2) A * dpow (t + 1) (-1 / 2) A * dpow (t + 1) 1 A = 1 := by
    rw [← dpow_add, ← dpow_add, show (-1 / 2 + -1 / 2 + 1 : ℝ) = 0 by norm_num, dpow_zero]
  calc _ = (dpow (i + 1) (-1 / 2) g * dpow (i + 1) (1 / 2) g) * (dpow (t + 1) (-1 / 2) A * dpow (t + 1) (-1 / 2) A * dpow (t + 1) 1 A) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = 1 := by rw [h1, h2, one_mul]

theorem equiv_eC {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (h : MirabolicParabolic k (i + 1) t) (m : Mir k ((i + 1) + t)) :
    eC ψ f ((h : Mir k ((i + 1) + t)) * m) = sigC τ σ h (eC ψ f m) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := _root_.borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI := isFinite_muD (k := k) (t + 1)
  obtain ⟨g, hg⟩ : ∃ g, g = (gpProj k (i + 1) t h).1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin (t + 1)) k, A = (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = sEmb k ((i + 1) + t) m := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂˣ, κ = dpow (i + 1) (1 / 2) g * dpow (t + 1) (-1 / 2) A := ⟨_, rfl⟩
  have hp := fun d => pointwise ψ f h y d
  rw [← hη, ← hg, ← hA, ← hκ] at hp
  obtain ⟨l, c⟩ := integrand_lc ψ hψ f y
  obtain ⟨l', c'⟩ := integrand_lc ψ hψ f (η * y)
  let T : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (psiN τ).V ⊗[ℂ] σ.V := (κ : ℂ) • ((sigC τ σ h) ∘ₗ (qC τ σ))
  have e1 : qC τ σ (intC ψ f (η * y)) = ((dpow (t + 1) 1 A : ℂˣ) : ℂ) • T (intC ψ f y) := by
    have a1 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) (qC τ σ) l' c'
    have a2 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T l c
    have a3 := smInt_scale A (T ∘ fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y))
      (IsLocallyConstant.comp l T) (c.comp_left (map_zero T))
    refine a1.symm.trans (Eq.trans ?_ (a3.trans (congrArg _ a2)))
    congr 1
    funext d
    have b := hp d
    rw [mul_assoc] at b
    simp only [Function.comp, map_smul]
    rw [b, hA, last_inv, ← hA]
    simp only [T, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, Units.smul_def]
  have key : (((dpow (i + 1) (-1 / 2) g * dpow (t + 1) (-1 / 2) A : ℂˣ) : ℂ)) * (((dpow (t + 1) 1 A : ℂˣ) : ℂ) * (κ : ℂ)) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (scalar_one g A)
    simpa only [Units.val_mul, Units.val_one, hκ] using this
  show ((dpowM ((i + 1) + t) (-1 / 2) ((h : Mir k ((i + 1) + t)) * m) : ℂˣ) : ℂ) •
      qC τ σ (intC ψ f (sEmb k _ ((h : Mir k ((i + 1) + t)) * m))) =
    sigC τ σ h (((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m)))
  rw [map_mul (sEmb k ((i + 1) + t)), ← hη, ← hy, e1, map_mul (dpowM ((i + 1) + t) (-1 / 2)), dpowM_hgp, ← hg, ← hA, map_smul]
  simp only [T, LinearMap.smul_apply, LinearMap.comp_apply, smul_smul, Units.val_mul] at key ⊢
  congr 1
  linear_combination ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) * key

theorem memC : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ),
    ∃ y : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), (y : smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).1.1 = eC ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f
  have hind : eC ψ f ∈ indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ) := fun h g => equiv_eC ψ hψ f h g
  have hsm : (⟨eC ψ f, hind⟩ : indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)) ∈ smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ)) := by
    show IsOpen {g | ind (MirabolicParabolic k (i + 1) t) (sigC τ σ) g ⟨eC ψ f, hind⟩ = ⟨eC ψ f, hind⟩}
    convert smooth_eC ψ τ σ f using 3 with g
    rw [Subtype.ext_iff, funext_iff]
    rfl
  obtain ⟨C, hC, hcov⟩ := cocompact (k := k) i t
  exact ⟨⟨⟨_, hsm⟩, C, hC, fun g _ => hcov g⟩, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.MemC
end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.root_map_mem_compact_of_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.uR_mem_KU | exact GlobalTheory.CompanionTheory.SwapRoot.uR_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.uR_mem_KU <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.simple_reflection_mem_maximal_compact : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), sR σ hU.1 a h ∈ KU σ n := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU | exact GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.simple_reflection_root_borel_decomp : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  first | exact @GlobalTheory.CompanionTheory.SwapFactor.sR_uR_factor | exact GlobalTheory.CompanionTheory.SwapFactor.sR_uR_factor | (intros; apply GlobalTheory.CompanionTheory.SwapFactor.sR_uR_factor <;> assumption)
end

section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.KunGlue

theorem slantOf : CrystallineSemistableComparison.Onto.TopRes → CrystallineSemistableComparison.Onto.SlantOf :=
  fun hT hS hM hC hZ hA hK => GlobalTheory.T.slant_of_hodge_kuenneth hT hS (fun K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP h₁ h₂ =>
    GlobalTheory.T.kuenneth_product_proper_smooth hS hM hC hZ hA hK K X X' P q q' p₁ p₂ hP h₁ h₂)

end GlobalTheory.CompanionTheory.KunGlue
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

theorem op_lie_single_neg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (i j : Fin a) (x : Cinf E) :
    π.op (.lie (toL (Matrix.single i j (-x)))) = -π.op (.lie (toL (Matrix.single i j x))) := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  change lieS E a i j (-x) φ.1 = -(lieS E a i j x φ.1)
  rw [map_neg]
  rfl

theorem EopV_adjoint : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (i j : Fin a) (φ ψ : π.V),
    B (EopV π τ i j φ) ψ = -B φ (EopV π (NumberField.ComplexEmbedding.conjugate τ) i j ψ) := by
  intro E _ _ _ a π B hB τ i j φ ψ
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  have c2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal _
  have s1 := hB.1 (toL (Matrix.single i j (atEmb τ 1))) φ ψ
  have s2 := hB.1 (toL (Matrix.single i j (atEmb τ Complex.I))) φ ψ
  simp only [EopV, e1, e2, op_lie_single_neg, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
    map_smul, map_sub, map_neg, map_smulₛₗ, c2, Complex.conj_I, smul_eq_mul, s1, s2, RingHom.id_apply, smul_neg,
    sub_neg_eq_add, map_add]
  ring

end GlobalTheory.CompanionTheory.ClozelHerm

end
end
