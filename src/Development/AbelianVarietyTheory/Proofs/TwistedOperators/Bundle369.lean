module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle346
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilRep_theta_datum_half_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ), (∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → ∀ (g : GA D S) (h : GA D T), (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) → ∀ c c' : ℂ, c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g⁻¹ h⁻¹ x) = c' * Φ x) → om (g, h) f = (c * c') • f := by
  first | exact @GlobalTheory.ThetaMove.om_theta_eq_smul | exact GlobalTheory.ThetaMove.om_theta_eq_smul | (intros; apply GlobalTheory.ThetaMove.om_theta_eq_smul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.LieEq

theorem exists_op {S S' Pi : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Pi] [Module ℂ Pi]
    (N : Submodule ℂ S) (N' : Submodule ℂ S') (p : S →ₗ[ℂ] Pi) (p' : S' →ₗ[ℂ] Pi) (δ : S →ₗ[ℂ] S) (δ' : S' →ₗ[ℂ] S')
    (h : ∀ f ∈ N, ∀ f' ∈ N', p f = p' f' → p (δ f) = p' (δ' f')) :
    ∃ A : Pi →ₗ[ℂ] Pi, (∀ f ∈ N, A (p f) = p (δ f)) ∧ ∀ f' ∈ N', A (p' f') = p' (δ' f') := by
  let L : (N × N') →ₗ[ℂ] Pi := p ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  let L₁ : (N × N') →ₗ[ℂ] Pi := p ∘ₗ δ ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ δ' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  have hk : LinearMap.ker L ≤ LinearMap.ker L₁ := by
    intro x hx
    simp only [LinearMap.mem_ker, L, L₁, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.coe_subtype] at hx ⊢
    have e : p (x.1 : S) = p' (-(x.2 : S')) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left hx
    have := h _ x.1.2 _ (N'.neg_mem x.2.2) e
    rw [this, map_neg, map_neg, neg_add_cancel]
  let A₀ : LinearMap.range L →ₗ[ℂ] Pi := (LinearMap.ker L).liftQ L₁ hk ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hA₀ : ∀ x, A₀ ⟨L x, LinearMap.mem_range_self L x⟩ = L₁ x := by
    intro x
    simp only [A₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨A, hA⟩ := LinearMap.exists_extend A₀
  have hA' : ∀ x, A (L x) = L₁ x := fun x => by
    rw [← hA₀ x, ← hA]; rfl
  refine ⟨A, fun f hf => ?_, fun f' hf' => ?_⟩
  · have := hA' (⟨f, hf⟩, 0)
    simpa [L, L₁] using this
  · have := hA' (0, ⟨f', hf'⟩)
    simpa [L, L₁] using this

end GlobalTheory.SquareAgree.LieEq

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open Finset
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramJacobi

theorem det_eq_of_cols_unit {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (h : ∀ i j, ¬ p j → M i j = (1 : Matrix n n R) i j) :
    M.det = (M.toSquareBlockProp p).det := by
  rw [← Matrix.det_transpose, Matrix.twoBlockTriangular_det (Matrix.transpose M) p]
  · have h1 : ((Matrix.transpose M).toSquareBlockProp fun i => ¬ p i) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.transpose_apply,
        Matrix.submatrix_apply]
      rw [h _ _ i.2, Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e.symm))]
    rw [h1, Matrix.det_one, mul_one, ← Matrix.det_transpose]
    rfl
  · intro i hi j hj
    rw [Matrix.transpose_apply, h _ _ hi, Matrix.one_apply_ne]
    rintro rfl
    exact hi hj

theorem jacobi_minor {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (G H : Matrix n n R) (hHG : H * G = 1) (p : n → Prop) [DecidablePred p] :
    (H.toSquareBlockProp fun i => ¬ p i).det * G.det = (G.toSquareBlockProp p).det := by
  have hGH : G * H = 1 := mul_eq_one_comm.mp hHG
  let N : Matrix n n R := Matrix.of fun i j => if p j then (1 : Matrix n n R) i j else H i j
  have hN : N.det = (H.toSquareBlockProp fun i => ¬ p i).det := by
    rw [Matrix.twoBlockTriangular_det N p]
    · have h1 : N.toSquareBlockProp p = 1 := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_pos j.2]
        rw [Matrix.one_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e))]
      have h2 : (N.toSquareBlockProp fun i => ¬ p i) = H.toSquareBlockProp fun i => ¬ p i := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_neg j.2]
      rw [h1, h2, Matrix.det_one, one_mul]
    · intro i hi j hj
      simp only [N, Matrix.of_apply, if_pos hj]
      rw [Matrix.one_apply_ne]
      rintro rfl
      exact hi hj
  have hGN : (G * N).det = (G.toSquareBlockProp p).det := by
    rw [det_eq_of_cols_unit (G * N) p]
    · have : (G * N).toSquareBlockProp p = G.toSquareBlockProp p := by
        ext i j
        simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.mul_apply, N, Matrix.of_apply, if_pos j.2, Matrix.one_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
    · intro i j hj
      rw [← hGH]
      simp only [Matrix.mul_apply, N, Matrix.of_apply, if_neg hj]
  rw [← hN, mul_comm, ← Matrix.det_mul, hGN]

end GlobalTheory.GramJacobi

namespace GlobalTheory.GramJacobi

end GlobalTheory.GramJacobi

namespace GlobalTheory

end GlobalTheory
end
