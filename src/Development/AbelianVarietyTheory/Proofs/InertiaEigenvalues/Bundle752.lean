module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle001
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWLagTerms.LagrangianFrames

section Blocks

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem row_rel (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    B * fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ = fromBlocks G⁻¹ 0 0 (-G⁻¹) := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have h1 : fromBlocks G 0 0 (-G) * fromBlocks G⁻¹ 0 0 (-G⁻¹) = 1 := by
    rw [fromBlocks_multiply]; simp [Matrix.mul_nonsing_inv _ hu, fromBlocks_one]
  have h2 : fromBlocks G⁻¹ 0 0 (-G⁻¹) * fromBlocks G 0 0 (-G) = 1 := by
    rw [fromBlocks_multiply]; simp [Matrix.nonsing_inv_mul _ hu, fromBlocks_one]
  have hL : (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * B = 1 := by
    calc (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * B
        = fromBlocks G⁻¹ 0 0 (-G⁻¹) * (Bᴴ * fromBlocks G 0 0 (-G) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB, h2]
  have hR : B * (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) = 1 := mul_eq_one_comm.1 hL
  calc B * fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ
      = B * (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * fromBlocks G⁻¹ 0 0 (-G⁻¹) := by
        simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    _ = fromBlocks G⁻¹ 0 0 (-G⁻¹) := by rw [hR, Matrix.one_mul]

theorem blocks_rel (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    B.toBlocks₁₁ * G⁻¹ * B.toBlocks₁₁ᴴ - B.toBlocks₁₂ * G⁻¹ * B.toBlocks₁₂ᴴ = G⁻¹ ∧
    B.toBlocks₁₁ * G⁻¹ * B.toBlocks₂₁ᴴ - B.toBlocks₁₂ * G⁻¹ * B.toBlocks₂₂ᴴ = 0 ∧
    B.toBlocks₂₁ * G⁻¹ * B.toBlocks₁₁ᴴ - B.toBlocks₂₂ * G⁻¹ * B.toBlocks₁₂ᴴ = 0 ∧
    B.toBlocks₂₁ * G⁻¹ * B.toBlocks₂₁ᴴ - B.toBlocks₂₂ * G⁻¹ * B.toBlocks₂₂ᴴ = -G⁻¹ := by
  have h := row_rel G hG B hB
  rw [← fromBlocks_toBlocks B, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, zero_sub, ← sub_eq_add_neg] at h
  exact h

end Blocks

section Blocks2

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem form_eq (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    (B.toBlocks₁₁ - B.toBlocks₂₁) * G⁻¹ * (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ =
      (B.toBlocks₂₂ - B.toBlocks₁₂) * G⁻¹ * (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ := by
  obtain ⟨h11, h12, h21, h22⟩ := blocks_rel G hG B hB
  set a := B.toBlocks₁₁
  set b := B.toBlocks₁₂
  set c := B.toBlocks₂₁
  set d := B.toBlocks₂₂
  rw [← sub_eq_zero, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub]
  have : (a - c) * G⁻¹ * (aᴴ - cᴴ) - (d - b) * G⁻¹ * (dᴴ - bᴴ) =
      (a * G⁻¹ * aᴴ - b * G⁻¹ * bᴴ) + (c * G⁻¹ * cᴴ - d * G⁻¹ * dᴴ) - (a * G⁻¹ * cᴴ - b * G⁻¹ * dᴴ) -
        (c * G⁻¹ * aᴴ - d * G⁻¹ * bᴴ) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [this, h11, h12, h21, h22]; abel

theorem adj_form (G : Matrix n n K) (hG : G.det ≠ 0) (hH : Gᴴ = G) (M : Matrix n n K) :
    (G⁻¹ * Mᴴ * G)ᴴ * G * (G⁻¹ * Mᴴ * G) = G * (M * G⁻¹ * Mᴴ) * G := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hH,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem ker_trivial (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) (v : n → K)
    (h1 : (G⁻¹ * (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ * G) *ᵥ v = 0)
    (h2 : (G⁻¹ * (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ * G) *ᵥ v = 0) : v = 0 := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hrow := row_rel G hG B hB
  set w := G *ᵥ v
  have k1 : (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ *ᵥ w = 0 := by
    have := congrArg (G *ᵥ ·) h1
    simpa [w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  have k2 : (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ *ᵥ w = 0 := by
    have := congrArg (G *ᵥ ·) h2
    simpa [w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  have hx : Bᴴ *ᵥ Sum.elim w (-w) = 0 := by
    rw [← fromBlocks_toBlocks B, fromBlocks_conjTranspose, fromBlocks_mulVec]
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mulVec] at k1 k2
    ext (i | i)
    · have := congrFun k2 i
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      simp only [Sum.elim_inl, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Pi.add_apply,
        Pi.neg_apply]
      linear_combination this
    · have := congrFun k1 i
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      simp only [Sum.elim_inr, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Pi.add_apply,
        Pi.neg_apply]
      linear_combination -this
  have hK : fromBlocks G⁻¹ 0 0 (-G⁻¹) *ᵥ Sum.elim w (-w) = 0 := by
    rw [← hrow, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hw : w = 0 := by
    have := congrArg (fun x => fromBlocks G 0 0 (-G) *ᵥ x) hK
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, fromBlocks_multiply] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.mul_nonsing_inv _ hu, neg_zero, fromBlocks_one, Matrix.one_mulVec] at this
    funext i; exact congrFun this (Sum.inl i)
  have : G⁻¹ *ᵥ w = v := by simp [w, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  rw [← this, hw, Matrix.mulVec_zero]

end Blocks2

variable {D : D7}

theorem unitary_of_mt (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (h : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) :
    g₀ᴴ * (GlobalTheory.Doubling.dblSp W).gram * g₀ = (GlobalTheory.Doubling.dblSp W).gram := by
  have hγ : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ) *
      (GlobalTheory.Doubling.dblSp W).gram.map (incA D) * Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ =
      (GlobalTheory.Doubling.dblSp W).gram.map (incA D) := γ.2
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g₀.map (incA D)) = g₀ᴴ.map (incA D) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    simp [sigR, CMData.sig, inclR]; rfl
  rw [h, hc, ← Matrix.map_mul, ← Matrix.map_mul] at hγ
  exact Matrix.map_injective
    (Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)) hγ

theorem star_dot' (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

theorem blk_unitary (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (h : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) :
    (blk W g₀)ᴴ * fromBlocks W.gram 0 0 (-W.gram) * blk W g₀ = fromBlocks W.gram 0 0 (-W.gram) := by
  have hU := unitary_of_mt W γ g₀ h
  rw [show (GlobalTheory.Doubling.dblSp W).gram = GlobalTheory.Doubling.dblGram finSumFinEquiv W.gram from GlobalTheory.Doubling.gram_hdbl W]
    at hU
  have := congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) hU
  simp only [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, Matrix.conjTranspose_submatrix,
    GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.submatrix_blkMat] at this
  exact this

theorem exists_lag_isLagFrame_frameOf (D : D7) (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∃ Y : Lag W, IsLagFrame W Y (frameOf W g₀) := by
  intro h
  have hB := blk_unitary W γ g₀ h
  have hG : (HSpace.gram W).det ≠ 0 := Formalism.L2.Theta.gram_det_ne W
  have hH : (HSpace.gram W)ᴴ = HSpace.gram W := Matrix.ext fun i j => W.herm.eq _ _
  set C := frameOf W g₀ with hC
  have h1 : C.1 = (HSpace.gram W)⁻¹ * ((blk W g₀).toBlocks₂₂ - (blk W g₀).toBlocks₁₂)ᴴ * HSpace.gram W := rfl
  have h2 : C.2 = (HSpace.gram W)⁻¹ * ((blk W g₀).toBlocks₁₁ - (blk W g₀).toBlocks₂₁)ᴴ * HSpace.gram W := rfl
  let φ : (Fin W.rank → D.host.E) →ₗ[D.host.E] (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) :=
    LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2)
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun v hv => ?_
    have e1 : C.1 *ᵥ v = 0 := congrArg Prod.fst hv
    have e2 : C.2 *ᵥ v = 0 := congrArg Prod.snd hv
    rw [h1] at e1
    rw [h2] at e2
    exact ker_trivial _ hG _ hB v e1 e2
  let Y : Lag W := ⟨LinearMap.range φ, by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    show star (C.1 *ᵥ x) ⬝ᵥ W.gram *ᵥ (C.1 *ᵥ y) = star (C.2 *ᵥ x) ⬝ᵥ W.gram *ᵥ (C.2 *ᵥ y)
    rw [star_dot', star_dot', h1, h2, adj_form _ hG hH, adj_form _ hG hH, form_eq _ hG _ hB]⟩
  refine ⟨Y, ?_⟩
  have hs := congrArg (Submodule.map φ) (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at hs
  refine Eq.trans ?_ hs
  congr 2
  funext j
  ext a <;> simp [φ, Matrix.mulVec, dotProduct, Pi.single_apply]

end GlobalTheory.SWLagTerms.LagrangianFrames
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section




namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem isHalf_sub' {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u - v) :=
  fun i j => by rw [Matrix.sub_apply, mul_sub, hu i j, hv i j]

theorem isHalf_nsmul'' {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu i j]

theorem frMapAdj_nsmul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    (n : ℕ) (x : WO S T) : frMapAdj S T βS βT (n • x) = n • frMapAdj S T βS βT x :=
  (AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_nsmul n x

theorem rdAdj_add (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x y : WO S T) :
    rdAdj S T βS βT φ (x + y) = rdAdj S T βS βT φ x + rdAdj S T βS βT φ y := by
  ext i j
  simp only [rdAdj, GlobalTheory.PlaceVec.frMapAdj_add, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem rdAdj_nsmul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (n : ℕ) (x : WO S T) :
    rdAdj S T βS βT φ (n • x) = n • rdAdj S T βS βT φ x :=
  (AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_nsmul n x

theorem rdAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x y : WO S T) :
    rdAdj S T βS βT φ (x - y) = rdAdj S T βS βT φ x - rdAdj S T βS βT φ y :=
  (AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_sub x y

theorem exists_natCast_dvd_pow (v : HeightOneSpectrum (𝓞 D.host.F)) {ϖ : GlobalTheory.SplitHecke.Ov D v} (hϖ : Irreducible ϖ)
    (m : ℕ) (hm : 0 < m) : ∃ N : ℕ, (m : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N := by
  have hne : (m : GlobalTheory.SplitHecke.Ov D v) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap D.host.F (Fv D.host.F v))] at h1
    have h2 := (algebraMap D.host.F (Fv D.host.F v)).injective (h1.trans (map_zero _).symm)
    exact hm.ne' (by exact_mod_cast h2)
  obtain ⟨N, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  exact ⟨N, (u : GlobalTheory.SplitHecke.Ov D v), hu.symm⟩

end GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

theorem sbHalf_locConst_cptSupp : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → ∀ ϖ : (GlobalTheory.SplitHecke.Ov D v), Irreducible ϖ → ∃ N : ℕ, (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), rdAdj S T βS βT φ x' = rdAdj S T βS βT φ x + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) → Φ x' = Φ x) ∧ ∀ x : WO S T, Φ x ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
  intro D S T βS βT e PP v φ ι he hL ΛS ΛT hS hT Φ hΦ ϖ hϖ
  obtain ⟨hsurj, hinj, hint, -⟩ := GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf D S T βS βT e PP v φ ι he hL
  obtain ⟨hsupp, k, hk, hinv, hkΛ⟩ := hΦ
  obtain ⟨K1, hK1, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨K2, hK2, hmem⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT
  obtain ⟨L1, hL1, hlat⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨L2, hL2, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
  have hce : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  obtain ⟨N, hN⟩ := exists_natCast_dvd_pow v hϖ (k * (K2 * K1) * (L2 * (L1 * k)))
    (by positivity)
  have hA : ((k * (K2 * K1) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N :=
    (Nat.cast_dvd_cast (Dvd.intro _ rfl)).trans hN
  have hM : ((L2 * (L1 * k) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N :=
    (Nat.cast_dvd_cast (Dvd.intro_left _ rfl)).trans hN
  refine ⟨N, ?_, ?_⟩
  · intro x x' hx hx' z hxz
    obtain ⟨w, hw⟩ := hA
    obtain ⟨t, ht, hrt⟩ := hsurj ((w • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have htI : IsIntM (frMapAdj S T βS βT t) := (hint t ht).2 ⟨w • z, hrt⟩
    have h1 := hdown t htI
    rw [← GlobalTheory.PlaceVec.map_toEAf_nsmul] at h1
    have h0 : (K1 • t).map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← ht i j, map_mul, hce, zero_mul, smul_zero, Matrix.zero_apply]
    have h2 := hmem _ h0 h1
    have hu : IsHalf (cA D e) (K2 • K1 • t) := isHalf_nsmul'' (isHalf_nsmul'' ht _) _
    have key : x' - x = k • (K2 • K1 • t) := by
      refine hinj _ _ (isHalf_sub' hx' hx) (isHalf_nsmul'' hu _) ?_
      rw [rdAdj_sub, hxz, add_sub_cancel_left, rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul, hrt, hw]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
      push_cast
      ring
    have : x' = x + k • (K2 • K1 • t) := by rw [← key]; abel
    rw [this, hinv _ h2 hu x]
  · intro x hx
    have hhalf := hsupp x hx
    have h1 := hlat _ (hkΛ x hx)
    rw [← GlobalTheory.PlaceVec.map_toEAf_nsmul] at h1
    have h2 := hup _ h1
    rw [← frMapAdj_nsmul] at h2
    obtain ⟨z0, hz0⟩ := (hint _ (isHalf_nsmul'' (isHalf_nsmul'' (isHalf_nsmul'' hhalf k) L1) L2)).1 h2
    rw [rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul] at hz0
    obtain ⟨w', hw'⟩ := hM
    refine ⟨w' • z0, ?_⟩
    ext i j
    have hij := congrFun (congrFun hz0 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at hij ⊢
    rw [hw', map_mul, map_mul, ← hij, map_natCast]
    push_cast
    ring

end GlobalTheory.DownLift.SplitCoef

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.TameRelation

open GlobalTheory.TameQuot

theorem eq_one_of_index_coprime {J N : Type} [Group J] [AddCommGroup N] {l k : ℕ}
    (hN : ∀ m : N, (l ^ k) • m = 0) (θ : J →* Multiplicative N) (h : θ.ker.index.Coprime l)
    (σ : J) : θ σ = 1 := by
  have h1 : θ σ ^ θ.ker.index = 1 := by
    rw [← map_pow]; exact θ.ker.pow_index_mem σ
  have h2 : θ σ ^ l ^ k = 1 := hN (θ σ).toAdd
  exact (pow_eq_one_iff_of_coprime (h.pow_right k)).1 ⟨h1, h2⟩

theorem pow_formula {Γ R W : Type} [Group Γ] [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : Representation R Γ W) {b : R} (hb : b * b = 0) {γ : Γ} (hγ : ∀ m, ρ γ m = m + b • m)
    (z : Γ → W) (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (k : ℕ) :
    (∀ m, ρ (γ ^ k) m = m + k • b • m) ∧ z (γ ^ k) = k • z γ + k.choose 2 • b • z γ := by
  have hbb : ∀ m : W, b • b • m = 0 := fun m => by rw [← mul_smul, hb, zero_smul]
  induction k with
  | zero => simpa using hz 1 1
  | succ k ih =>
    refine ⟨fun m => ?_, ?_⟩
    · rw [pow_succ', map_mul, Module.End.mul_apply, ih.1, hγ, smul_add, smul_comm b k, hbb,
        smul_zero, add_zero, succ_nsmul]
      abel
    · rw [pow_succ', hz, ih.2, hγ, smul_add, smul_comm b k, smul_comm b (k.choose 2), hbb,
        smul_zero, add_zero, succ_nsmul, Nat.choose_succ_succ' k 1, Nat.choose_one_right, add_smul]
      abel

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (k : ℕ), normV v % (2 * l ^ k) = 1 → ∀ (M : ℕ) (d : G F Ω →* Multiplicative (ZMod (l ^ M))) (γ σ : G F Ω), 1 ≤ M → IsOpen (d.ker : Set (G F Ω)) → γ ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) σ → ∀ (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R (G F Ω) W) (a b : R), (∀ m : W, (l ^ k) • m = 0) → b * b = 0 → (∀ τ ∈ Ine (F := F) A, ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m) → (∀ m, ρ σ m = m + a • m) → ∀ z : Z1 ρ, a • z.1 γ = b • z.1 σ ∧ (b = 0 → z.1 γ = 0 → ∀ τ ∈ Ine (F := F) A, z.1 τ = 0) := by
  intro hT F Ω _ _ _ _ _ l hlp A v hA hl k hq M d γ σ hM hd hγ hdγ hσ R _ W _ _ _ _ ρ a b h4 hb hI hρ z
  obtain ⟨-, -, hco, ⟨t, tc, ts, hk⟩, -, -⟩ := hT F Ω l A v hA hl
  haveI : Fact (1 < l ^ M) := ⟨one_lt_pow₀ hlp.out.one_lt (by omega)⟩
  have hdJ : ∀ τ ∈ ineKer F A l, d τ = 1 := fun τ hτ =>
    eq_one_of_index_coprime (l := l) (k := M) (fun m => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
      (d.comp (ineKer F A l).subtype) (hco _ inferInstance (hd.preimage continuous_subtype_val)) ⟨τ, hτ⟩
  have hρJ : ∀ τ ∈ ineKer F A l, ∀ m, ρ τ m = m := fun τ hτ m => by
    rw [hI τ (ineKer_le_Ine A l hτ), hdJ τ hτ]; simp
  have hzJ : ∀ τ ∈ ineKer F A l, z.1 τ = 0 := fun τ hτ => by
    let θ : ineKer F A l →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hρJ _ g.2] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (ineKer F A l)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    exact eq_one_of_index_coprime (l := l) (k := k) h4 θ
      (hco _ inferInstance ho) ⟨τ, hτ⟩
  refine ⟨?_, fun hb0 h0 τ hτ => ?_⟩
  · have hj := tame_rel hA hl hσ hγ
    have hγ' : ∀ m, ρ γ m = m + b • m := fun m => by
      rw [hI γ hγ, hdγ, toAdd_ofAdd, ZMod.val_one, Nat.cast_one, one_mul]
    obtain ⟨p1, p2⟩ := pow_formula ρ hb hγ' z.1 z.2.2 (normV v)
    have hqs : ∀ m : W, normV v • m = m := KStar.Tree.nsmul_eq_self_of_mod hq h4
    obtain ⟨c, hc⟩ := KStar.Tree.dvd_choose_two hq
    rw [hc, mul_comm (l ^ k), mul_smul, h4, smul_zero, add_zero, hqs] at p2
    have e : σ * γ = γ ^ normV v * (((γ ^ normV v)⁻¹ * (σ * γ * σ⁻¹)) * σ) := by group
    have h1 := z.2.2 σ γ
    rw [e, z.2.2, z.2.2 _ σ, hzJ _ hj, hρJ _ hj, zero_add, p1, p2, hqs, hρ, ← add_assoc,
      ← add_assoc, add_comm (z.1 γ)] at h1
    exact (add_left_cancel h1).symm
  · have hg : IsProGen F A l γ := by
      refine (isProGen_iff_isUnit F Ω l A t tc ts hk ⟨γ, hγ⟩).2 ?_
      by_contra hu
      obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.mem_nonunits.1 hu)
      obtain ⟨g, hg⟩ := ts (Multiplicative.ofAdd y)
      have h1 : t ((g ^ l)⁻¹ * ⟨γ, hγ⟩) = 1 := by
        rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hg]
        refine Multiplicative.toAdd.injective ?_
        rw [hy, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]
      have h2 : d (((g : G F Ω) ^ l)⁻¹ * γ) = 1 := hdJ _ ((hk _).1 h1)
      rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hdγ] at h2
      have h3 := congrArg (fun x => ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) (ZMod l)
        (Multiplicative.toAdd x)) h2
      simp only [toAdd_pow, toAdd_ofAdd, map_one, nsmul_eq_mul, map_mul, map_natCast,
        ZMod.natCast_self, zero_mul] at h3
      exact zero_ne_one h3
    let θ : Ine (F := F) A →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hI _ g.2, hb0, mul_zero, zero_smul, add_zero] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hzJ τ hτ, rfl⟩
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hg.2 hτ)
    exact hτ'

end GlobalTheory.TameRelation
end

section

open NumberField

theorem _root_.GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → Submodule.IsFullLattice E M → Submodule.IsFullLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') → (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) → ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  first
  | exact @GlobalTheory.NabScale.nabAtr_smul_pow_mem
  | intro E K _ _ _ _ ι _ n emb lam M M' N hN hM hM' h1 h2
    exact GlobalTheory.NabScale.nabAtr_smul_pow_mem E K ι n emb lam M M' N hN
      hM.toIsLattice hM'.toIsLattice h1 h2
end
