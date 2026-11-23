module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.MemHeadColsIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def GramUnitG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh Z Zσ →
    IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det

def StepDuF : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ γ' : IsoMbe Zσ₁.Z Zσ₂.Z,
      ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
        Ind hs γ θ₁ → Ind hs γ' θ₂ →
        ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
          θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
          dotProduct (uV g l₂) (Matrix.mulVec (gHat g Zh₂ T T')⁻¹ (uV g w₂)) -
            dotProduct (uV g l) (Matrix.mulVec (gHat g Zh₁ T T')⁻¹ (uV g w)) ∈ 𝒪[F]

theorem stepDu_of (hU : GramUnitG) (h : StepDuF) : StepDu := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk γ
  obtain ⟨γ', hγ'⟩ := h F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk γ
  exact ⟨γ', fun θ₁ θ₂ i₁ i₂ => isoB_of hs Zh₁ Zh₂ T T'
    (hU F E M g r T T' TT Zh₁ Z₁ Zσ₁ h₁) (hU F E M g r T T' TT Zh₂ Z₂ Zσ₂ h₂) θ₁ θ₂ (hγ' θ₁ θ₂ i₁ i₂)⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def lamL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : (Fin (r + 1) → O) →ₗ[O] E where
  toFun y := lamC (Z.map O.subtype) (fun j => (y j : E))
  map_add' a b := by simp [lamC, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [lamC, Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]

theorem lamL_apply (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y : Fin (r + 1) → O) :
    lamL O Z y = lamC (Z.map O.subtype) (fun j => (y j : E)) := rfl

theorem lamL_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (w : Fin (r + 1) → O) : lamL O Z (Z.mulVec w) = (w (Fin.last r) : E) := by
  rw [lamL_apply, lamC]
  have hv : (fun j => ((Z.mulVec w j : O) : E)) = (Z.map O.subtype).mulVec (fun j => (w j : E)) := by
    funext j
    exact RingHom.map_mulVec O.subtype Z w j
  rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem lamL_K (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (k : Fin (r + 1) → O) (hk : k ∈ headCols Z) : lamL O Z k = 0 := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z k).1 hk
  rw [lamL_mulVec O Z hu, hw]; rfl

theorem bvec_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    (fun i => Z i (Fin.last r)) = Z.mulVec (Pi.single (Fin.last r) 1) := col_eq_mulVec Z _

theorem lamL_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) :
    lamL O Z (fun i => Z i (Fin.last r)) = 1 := by
  rw [bvec_eq, lamL_mulVec O Z hu]; simp

theorem det_smul_mk' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (v : Fin (r + 1) → O) :
    Z.det • (Submodule.Quotient.mk v : MbMod Z) =
      (Z.adjugate.mulVec v) (Fin.last r) • bCls Z := by
  rw [← Submodule.Quotient.mk_smul, bCls, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  set u := Z.adjugate.mulVec v
  have hdv : Z.det • v = Z.mulVec u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hdv, bvec_eq, ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  exact (mem_headCols_iff Z _).mpr ⟨_, by simp, rfl⟩

theorem det_coe (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : ((Z.det : O) : E) = (Z.map O.subtype).det := by
  exact RingHom.map_det O.subtype Z

theorem det_mul_lamL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (v : Fin (r + 1) → O) :
    (Z.det : E) * lamL O Z v = ((Z.adjugate.mulVec v) (Fin.last r) : E) := by
  rw [det_coe, lamL_apply, lamC, Matrix.inv_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
  have h1 := RingHom.map_mulVec O.subtype Z.adjugate v (Fin.last r)
  have h2 := RingHom.map_adjugate O.subtype Z
  simp only [RingHom.mapMatrix_apply] at h2
  rw [← h2] at *
  exact h1.symm

theorem lam_keep {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (hu₁ : IsUnit (Z₁.map O.subtype).det)
    (hu₂ : IsUnit (Z₂.map O.subtype).det) (γ : MbMod Z₁ →ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (y₁ y₂ : Fin (r + 1) → O)
    (h : γ (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y₂) : lamL O Z₂ y₂ = lamL O Z₁ y₁ := by
  let Λ := (headCols Z₂).liftQ (lamL O Z₂) (fun k hk => LinearMap.mem_ker.mpr (lamL_K O Z₂ hu₂ k hk))
  have hΛb : Λ (bCls Z₂) = 1 := lamL_b O Z₂ hu₂
  have hΛy : Λ (Submodule.Quotient.mk y₂) = lamL O Z₂ y₂ := rfl
  have key := congrArg (fun q => Λ (γ q)) (det_smul_mk' O Z₁ y₁)
  simp only [map_smul, hb, h, hΛb, hΛy] at key
  have hdet : IsUnit ((Z₁.det : O) : E) := by rw [det_coe]; exact hu₁
  apply hdet.mul_left_cancel
  rw [det_mul_lamL O Z₁ hu₁ y₁]
  rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, mul_one] at key
  exact key

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end
