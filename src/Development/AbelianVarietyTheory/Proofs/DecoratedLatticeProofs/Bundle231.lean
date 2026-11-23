module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle148
public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle413
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle197
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

end Global

end GlobalTheory.PlaceCompare.Spherical

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

noncomputable section
namespace GlobalTheory.FrameNorm

open Formalism.L2.Theta (mt)



theorem norm : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), ∀ δ ∈ GQ V,
    ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) →
    ∀ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G → δ₀ * C = C * G → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  intro D V r C δ hδ δ₀ hδ₀ G hG hC
  obtain ⟨g, hg, e1, e2⟩ := exists_rat V hδ
  have hg0 : (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = δ₀ := by
    apply Matrix.map_injective (GlobalTheory.FrameStab.incA_injective D)
    exact e1.symm.trans hδ₀
  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = V.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r) (Fin V.rank) D.host.E, P = Formalism.UG.cT σ C * J := ⟨_, rfl⟩
  obtain ⟨δi, hδi⟩ : ∃ δi : Matrix (Fin V.rank) (Fin V.rank) D.host.E, δi = (g⁻¹ : GL (Fin V.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hδδi : δ₀ * δi = 1 := by rw [← hg0, hδi]; exact Units.mul_inv g
  have hδiδ : δi * δ₀ = 1 := by rw [← hg0, hδi]; exact Units.inv_mul g
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hU : Formalism.UG.cT σ δ₀ * J * δ₀ = J := by rw [← hg0, hσ, hJ]; exact hg
  have hiC : δi * C = C * G⁻¹ := by
    calc δi * C = δi * (C * G * G⁻¹) := by rw [Matrix.mul_assoc C, hGGi, Matrix.mul_one]
      _ = δi * (δ₀ * C) * G⁻¹ := by rw [← hC]; simp only [Matrix.mul_assoc]
      _ = C * G⁻¹ := by rw [← Matrix.mul_assoc δi, hδiδ, Matrix.one_mul]
  have hc1 : Formalism.UG.cT σ δi * Formalism.UG.cT σ δ₀ = 1 := by
    rw [← Formalism.UG.cT_mul, hδδi]; simp [Formalism.UG.cT]
  have hcG : Formalism.UG.cT σ G * Formalism.UG.cT σ G⁻¹ = 1 := by
    rw [← Formalism.UG.cT_mul, hGiG]; simp [Formalism.UG.cT]
  have hJδ : J * δ₀ = Formalism.UG.cT σ δi * J := by
    calc J * δ₀ = Formalism.UG.cT σ δi * Formalism.UG.cT σ δ₀ * J * δ₀ := by rw [hc1, Matrix.one_mul]
      _ = Formalism.UG.cT σ δi * (Formalism.UG.cT σ δ₀ * J * δ₀) := by simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ δi * J := by rw [hU]
  have hPδ : P * δ₀ = Formalism.UG.cT σ G⁻¹ * P := by
    calc P * δ₀ = Formalism.UG.cT σ C * (J * δ₀) := by rw [hP, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (δi * C) * J := by rw [hJδ, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ G⁻¹ * P := by rw [hiC, Formalism.UG.cT_mul, hP, Matrix.mul_assoc]
  have hPδi : P * δi = Formalism.UG.cT σ G * P := by
    calc P * δi = Formalism.UG.cT σ G * Formalism.UG.cT σ G⁻¹ * P * δi := by rw [hcG, Matrix.one_mul]
      _ = Formalism.UG.cT σ G * (P * δ₀) * δi := by rw [hPδ]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ G * P := by simp only [Matrix.mul_assoc, hδδi, Matrix.mul_one]

  have hΔ : mt V δ = δ₀.map (incA D) := hδ₀
  have hΔi : mt V δ⁻¹ = δi.map (incA D) := by rw [hδi]; exact e2
  have hΓiL : mt V δ⁻¹ * C.map (incA D) = C.map (incA D) * (G⁻¹).map (incA D) := by
    rw [hΔi, ← Matrix.map_mul, hiC, Matrix.map_mul]
  have hPΓ : P.map (incA D) * mt V δ = (Formalism.UG.cT σ G⁻¹).map (incA D) * P.map (incA D) := by
    rw [hΔ, ← Matrix.map_mul, hPδ, Matrix.map_mul]
  have key : NI V C ≤ (NI V C).comap (MulAut.conj δ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (mt V m - 1) * C.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) * (mt V m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hJ]; exact this
    have h3 : ∀ x : Fin V.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin r → AE D,
        (mt V m - 1) *ᵥ (fun i => incA D (x i)) = C.map (incA D) *ᵥ a := by
      rw [hP, hσ, hJ]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
    · show (mt V (δ * m * δ⁻¹) - 1) * C.map (incA D) = 0
      rw [GlobalTheory.FrameStab.mt_conj_sub_one]
      simp only [Matrix.mul_assoc]
      rw [hΓiL, ← Matrix.mul_assoc (mt V m - 1), h1, Matrix.zero_mul, Matrix.mul_zero]
    · have c2 : P.map (incA D) * (mt V (δ * m * δ⁻¹) - 1) = 0 := by
        rw [GlobalTheory.FrameStab.mt_conj_sub_one]
        simp only [← Matrix.mul_assoc]
        rw [hPΓ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P.map (incA D)) (mt V m - 1), h2, Matrix.zero_mul, Matrix.mul_zero]
      rw [hP, hσ, hJ] at c2; exact c2
    · intro x hx
      rw [← hJ, ← hσ, ← hP] at hx
      have hy : P *ᵥ (δi *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hPδi, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 _ hy
      refine ⟨G.map (incA D) *ᵥ a, ?_⟩
      have hxi : mt V δ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((δi *ᵥ x) i) := by
        rw [hΔi]; funext i; exact (RingHom.map_mulVec (incA D) δi x i).symm
      show (mt V (δ * m * δ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = C.map (incA D) *ᵥ (G.map (incA D) *ᵥ a)
      rw [GlobalTheory.FrameStab.mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha,
        Matrix.mulVec_mulVec, hΔ, ← Matrix.map_mul, hC, Matrix.map_mul, Matrix.mulVec_mulVec]
  intro n hn
  exact key hn

end GlobalTheory.FrameNorm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ParabIndex

theorem card_GL_real (κ : Type) [Field κ] [Finite κ] (m : ℕ) :
    (Nat.card (GL (Fin m) κ) : ℝ)
      = (Nat.card κ : ℝ) ^ (m * m) * ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  letI := Fintype.ofFinite κ
  rw [GlobalTheory.Mem.card_GL_eq_pow_mul_qE κ m, Nat.card_eq_fintype_card, Formalism.MainNotions.ZetaProductPairs.qE]
  congr 1
  have h : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [_root_.zpow_neg, zpow_natCast]

variable {κ : Type} [Field κ]

theorem val_mk' {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι κ) (h : IsUnit A.det) :
    ((Matrix.GeneralLinearGroup.mk'' A h : GL ι κ) : Matrix ι ι κ) = A := rfl

def toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) κ :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (g : Matrix (Fin (r + s)) (Fin (r + s)) κ)

theorem isUnit_det_toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : IsUnit (toSum g).det := by
  rw [toSum, Matrix.det_reindex_self]
  exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

theorem mem_blockUpperTriangularTwo_iff_lowerLeft_zero {r s : ℕ} (g : GL (Fin (r + s)) κ) :
    g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ (toSum g).toBlocks₂₁ = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h
    ext i j
    simp only [toSum, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, Matrix.zero_apply]
    apply h
    simp [Formalism.L2.DIV.blk2]
  · intro h i j hij
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
    rcases x with x | x <;> rcases y with y | y
    · simp [Formalism.L2.DIV.blk2] at hij
    · simp [Formalism.L2.DIV.blk2] at hij
    · have := congrFun (congrFun h x) y
      simpa [toSum, Matrix.toBlocks₂₁] using this
    · simp [Formalism.L2.DIV.blk2] at hij

theorem toSum_eq_fromBlocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    toSum g = Matrix.fromBlocks (toSum g).toBlocks₁₁ (toSum g).toBlocks₁₂ 0 (toSum g).toBlocks₂₂ := by
  rw [← (mem_blockUpperTriangularTwo_iff_lowerLeft_zero g).1 hg]; exact (Matrix.fromBlocks_toBlocks _).symm

theorem isUnit_blocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    IsUnit ((toSum g).toBlocks₁₁.det * (toSum g).toBlocks₂₂.det) := by
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (toSum g).toBlocks₁₂, ← toSum_eq_fromBlocks hg]
  exact isUnit_det_toSum g

theorem isUnit_det_fromBlocks {r s : ℕ} (A : GL (Fin r) κ) (D : GL (Fin s) κ) (B : Matrix (Fin r) (Fin s) κ) :
    IsUnit (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin s) (Fin s) κ))).det := by
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit)

noncomputable def blockTriangularEquiv (r s : ℕ) :
    Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r) ≃
      GL (Fin r) κ × GL (Fin s) κ × Matrix (Fin r) (Fin s) κ where
  toFun g :=
    (Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left (isUnit_blocks g.2)),
     Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right (isUnit_blocks g.2)),
     (toSum g.1).toBlocks₁₂)
  invFun x := ⟨Matrix.GeneralLinearGroup.mk'' _ (isUnit_det_fromBlocks x.1 x.2.1 x.2.2), by
    rw [mem_blockUpperTriangularTwo_iff_lowerLeft_zero]
    ext i j
    simp [toSum, Matrix.toBlocks₂₁, val_mk']⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    show Matrix.reindex finSumFinEquiv finSumFinEquiv _ = _
    have h := toSum_eq_fromBlocks g.2
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (toSum g.1).toBlocks₁₁ (toSum g.1).toBlocks₁₂ 0 (toSum g.1).toBlocks₂₂) = _
    rw [← h, toSum]
    simp
  right_inv x := by
    rcases x with ⟨A, D, B⟩
    refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_)
    · show (toSum _).toBlocks₁₁ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₁, val_mk']
    · show (toSum _).toBlocks₂₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₂₂, val_mk']
    · show (toSum _).toBlocks₁₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₂, val_mk']

theorem natCard_blockUpperTriangularTwo_finiteField (κ : Type) [Field κ] [Finite κ] (r s : ℕ) :
    Nat.card (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)) =
      Nat.card (GL (Fin r) κ) * Nat.card (GL (Fin s) κ) * Nat.card κ ^ (r * s) := by
  rw [Nat.card_congr (blockTriangularEquiv r s), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin s → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.ParabIndex

namespace GlobalTheory.ParabIndex

theorem index_maxParabolic_GL_finiteField : ∀ (κ : Type) [Field κ] [Finite κ] (n r s : ℕ), n = r + s → (((Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin n) κ)).index : ℕ) : ℝ) = (Nat.card κ : ℝ) ^ (r * s) * (∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) / ((∏ i ∈ Finset.Ioc 0 r, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) * ∏ i ∈ Finset.Ioc 0 s, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) := by
  intro κ _ _ n r s hn
  subst hn
  have hmul := (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).card_mul_index
  rw [natCard_blockUpperTriangularTwo_finiteField] at hmul
  have hR : (((Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).index : ℕ) : ℝ) *
      ((Nat.card (GL (Fin r) κ) : ℝ) * (Nat.card (GL (Fin s) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * s))
      = (Nat.card (GL (Fin (r + s)) κ) : ℝ) := by
    rw [mul_comm]; exact_mod_cast hmul
  have hGr : (Nat.card (GL (Fin r) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hGs : (Nat.card (GL (Fin s) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [card_GL_real] at hGr hGs
  rw [card_GL_real, card_GL_real, card_GL_real] at hR
  have hq : (Nat.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hPr := right_ne_zero_of_mul hGr
  have hPs := right_ne_zero_of_mul hGs
  rw [eq_div_iff (mul_ne_zero hPr hPs)]
  have key : (r + s) * (r + s) = r * r + s * s + r * s + r * s := by ring
  rw [key, pow_add, pow_add, pow_add] at hR
  have hX : (Nat.card κ : ℝ) ^ (r * r) * (Nat.card κ : ℝ) ^ (s * s) * (Nat.card κ : ℝ) ^ (r * s) ≠ 0 := by
    have := pow_ne_zero (r * r) hq; have := pow_ne_zero (s * s) hq; have := pow_ne_zero (r * s) hq
    positivity
  apply mul_right_cancel₀ hX
  linear_combination hR

end GlobalTheory.ParabIndex
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (s : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (s • f) = s • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7} {m n : ℕ}

theorem dRho_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (s : ℂ) (f : Mx D m n → ℂ) :
    Datum.dRho hs θ τ z (s • f) = s • Datum.dRho hs θ τ z f := by
  funext x
  simp only [Datum.dRho, hh, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field _

theorem aPlusAll_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k) (s : ℂ) (f : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (s • f) = s • aPlusAll hs θ J B B' k f := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hh, smul_sub, smul_comm s]

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (k : ι →₀ ℕ) (s : ℂ) (f : X → ℂ) : opPow A k (s • f) = s • opPow A k f := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (s : ℂ) (f : X → ℂ) : pureTensorL A (s • f) = s • pureTensorL A f := by
  unfold pureTensorL
  have : (fun k : ι →₀ ℕ => opPow A k (s • f)) = s • fun k => opPow A k f := by
    funext k; exact opPow_smul A hA k s f
  rw [this, map_smul]

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (s : ℂ) (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (s • f) = s • pureTensorO ψ θ S T sS sT BS BT f :=
  pureTensorL_smul _ (aPlusAll_smul _ (heisO_smul ψ S T) _ _ _ _) s f

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

end GlobalTheory.SeeSaw.Resc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory

theorem finite_monomials_of_placeDegree : ∀ (D : D7) (m n : ℕ) (d : D.what₂.Tau → ℕ), {α : FVar D m n →₀ ℕ | ∀ τ, (∑ v ∈ α.support with v.1 = τ, α v) = d τ}.Finite := by
  intro D m n d
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : FVar D m n => d v.1))).subset ?_
  intro α hα
  simp only [Set.mem_setOf_eq] at hα
  rw [Set.mem_Iic, Finsupp.le_def]
  intro v
  rw [Finsupp.coe_equivFunOnFinite_symm]
  by_cases hv : v ∈ α.support
  · rw [← hα v.1]
    exact Finset.single_le_sum (f := fun w => α w) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨hv, rfl⟩)
  · rw [Finsupp.notMem_support_iff.1 hv]
    exact Nat.zero_le _

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ (g : GA D S) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), ∑ i, a i • heisO ψ S T (y i) F = F → ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F = 0 → ∫ w in X, om (g, 1) F w * conj (F w) ∂m = 0 := by
  first | exact @GlobalTheory.ChainOnto.coef_zero_of_heis_relations | exact GlobalTheory.ChainOnto.coef_zero_of_heis_relations | (intros; apply GlobalTheory.ChainOnto.coef_zero_of_heis_relations <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Z : Finset (Pl D.host.E)), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, Lev.finE V k ∈ Formalism.L2.DIV.St β ∧ ∀ PP ∈ Z, Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.ChainOnto.LevelOpen.exists_open_princ | exact GlobalTheory.ChainOnto.LevelOpen.exists_open_princ | (intros; apply GlobalTheory.ChainOnto.LevelOpen.exists_open_princ <;> assumption)
end
