module

import Formalism.LocalToGlobal.IndefiniteReal.OpNormAtLeOfPoints
public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.Bundle001
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
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.StatementLat

@[expose] public section

section

set_option linter.deprecated false

open Module NumberField

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration

theorem dense_emb {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  apply Formalism.IndefR.LatticeTransfer.BlockMetrics.dense_emb <;> assumption

theorem dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  apply Formalism.IndefR.LatticeTransfer.BlockMetrics.dense_fcoord <;> assumption

private theorem vecAt_apply_linearMap {K V ι W κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V)
    (b' : Basis κ K W) (φ : V →ₗ[K] W) (v : InfinitePlace K) (f : V) :
    Formalism.HermitianLatticesTheory.vecAt b' v (φ f) = Matrix.mulVec ((LinearMap.toMatrix b b' φ).map v.embedding) (Formalism.HermitianLatticesTheory.vecAt b v f) := by
  funext i
  simp only [Formalism.HermitianLatticesTheory.vecAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b' φ f, RingHom.map_mulVec]
  rfl

theorem opNormAt_le_of_points {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K]
    [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] W) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b' X' v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b' X' v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun y => ?_
  have hd := dense_fcoord b X hX v
  refine hd.induction_on (p := fun y => ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v)) y‖ ≤ C * ‖y‖) y ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hn : ∀ (κ' : Type) [Fintype κ'] (u : κ' → ℂ), ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ')‖ = Formalism.HermitianLatticesTheory.cnorm u := by
      intro κ' _ u
      rw [EuclideanSpace.norm_eq]
      rfl
    have hm : Matrix.mulVec ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) (Formalism.HermitianLatticesTheory.fcoord b X v f) =
        Formalism.HermitianLatticesTheory.fcoord b' X' v (φ f) := by
      simp only [Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ (hX v)]
      rw [vecAt_apply_linearMap b b' φ v f, Matrix.mulVec_mulVec]
    simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin, Matrix.toLpLin_toLp,
      Matrix.toLin'_apply, hm, hn, Formalism.HermitianLatticesTheory.normAt] using h f

end Formalism.L2.Geo.ExtensionFiltration
end
end

section

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  (K' : Type) [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']

abbrev ext (A : HLat K) (N : Submodule (𝓞 K) A.V) : Submodule (𝓞 K') (baseChange K' A).V :=
  (baseChange K' (withL A N)).L

def tau (A : HLat K) (σ : K' ≃ₐ[K] K') : (baseChange K' A).V ≃ₗ[K] (baseChange K' A).V :=
  TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl K A.V)
end

def S2 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K) (M N : Submodule (𝓞 K) A.V), N.FG → M ≤ N →
  M.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 →
  (ext K' A M).toAddSubgroup.relIndex (ext K' A N).toAddSubgroup ≠ 0 ∧
  (ext K' A M).toAddSubgroup.relIndex (ext K' A N).toAddSubgroup ≤
    M.toAddSubgroup.relIndex N.toAddSubgroup ^ finrank K K'

def GaloisDescentSubspaces : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K'] [IsGalois K K']
  (A : HLat K) (W : Submodule K' (K' ⊗[K] A.V)),
  (∀ (σ : K' ≃ₐ[K] K') (y : K' ⊗[K] A.V), y ∈ W → tau K' A σ y ∈ W) →
  ∃ W₀ : Submodule K A.V, W = W₀.baseChange K'

def ExtensionInterSubspace : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K), A.L.FG → ∀ (W₀ : Submodule K A.V), W₀ ≤ Submodule.span K (A.L : Set A.V) →
  ∀ (y : (baseChange K' A).V),
  y ∈ (baseChange K' A).L → (y : K' ⊗[K] A.V) ∈ W₀.baseChange K' →
  y ∈ ext K' A (A.L ⊓ W₀.restrictScalars (𝓞 K))

end Formalism.L2.Geo.ExtensionFiltration.ExtInvSk
end
end
