module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

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

namespace GlobalTheory.Core.Rk.Dich

theorem exists_mem_siegel_of_diagSnd : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → x = 0) → ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V := by
  intro D V γ hγ γi hγi hinj
  have hinc : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, hg, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective hinc (hγi.symm.trans hg2)
  have hgγ : g.1 * γi = 1 := by rw [hγi']; exact Units.mul_inv g
  have hgi : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h := inv_mem hg
    change Formalism.UG.cT _ (g⁻¹).1 * (dblSp V).gram * (g⁻¹).1 = (dblSp V).gram at h
    rw [gram_hdbl] at h
    rw [hγi']; exact h
  have hiso := isotropic_diag hgi
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set P := leviMat finSumFinEquiv γi with hP
  set Q := diagSnd γi with hQ
  have hQu : IsUnit Q := Matrix.mulVec_injective_iff_isUnit.1 fun x y h =>
    sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hQ1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)
  have hcT : ∀ M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E,
      Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
    intro M N; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcT1 : Formalism.UG.cT σ Q⁻¹ * Formalism.UG.cT σ Q = 1 := by
    rw [← hcT, hQ1]; simp [Formalism.UG.cT]
  have hδ : Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹) = V.gram := by
    calc Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹)
        = Formalism.UG.cT σ Q⁻¹ * (Formalism.UG.cT σ P * V.gram * P) * Q⁻¹ := by simp only [hcT, Matrix.mul_assoc]
      _ = V.gram := by
        rw [hiso]; simp only [Matrix.mul_assoc]
        rw [hQ1, Matrix.mul_one, ← Matrix.mul_assoc, hcT1, Matrix.one_mul]
  have hdet : IsUnit (P * Q⁻¹).det := by
    have h := congrArg Matrix.det hδ
    rw [Matrix.det_mul, Matrix.det_mul] at h
    have hJ : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
    rw [← h] at hJ
    exact isUnit_of_mul_isUnit_right hJ
  set d : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det (P * Q⁻¹)).2 hdet).unit with hd
  have hdv : d.1 = P * Q⁻¹ := rfl
  have hdU : d ∈ Formalism.UG.UJ σ V.gram := by
    change Formalism.UG.cT σ d.1 * V.gram * d.1 = V.gram
    rw [hdv]; exact hδ
  obtain ⟨δ', hδ'Q, hδ'⟩ := exists_of_rat V hdU
  refine ⟨δ'⁻¹, inv_mem hδ'Q, ?_⟩
  rw [show (io V (δ'⁻¹, 1))⁻¹ = io V (δ', 1) by rw [← map_inv, Prod.inv_mk, inv_inv, inv_one]]
  have hm : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1 =
      (g.1 * blkMat finSumFinEquiv (P * Q⁻¹) 1).map (incA D) := by
    rw [map_mul, Units.val_mul, hg1, matHom_io, val_blkGL, hδ', map_one, Units.val_one, hdv]
    conv_rhs => rw [Matrix.map_mul, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  refine mem_siegelOf.2 ?_
  change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1
  rw [hm]
  refine KeepsDiag.map _ (keepsDiag_of_mulVec fun w hw => ?_) _
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  rw [← Matrix.mulVec_mulVec, blkMat_mulVec, Matrix.one_mulVec]
  have h2 : pairVec finSumFinEquiv ((P * Q⁻¹) *ᵥ x) x = γi *ᵥ pairVec finSumFinEquiv (Q⁻¹ *ᵥ x) (Q⁻¹ *ᵥ x) := by
    rw [mulVec_pairVec_diag, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_mulVec, hgγ, Matrix.one_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

end GlobalTheory.Core.Rk.Dich
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

namespace GlobalTheory.Core.Rk.Dich

theorem matHom_conj_io (D : D7) (V : HSp D) (γ : GA D (dblSp V)) (δ : GA D V) (g : GL (Fin (V.rank + V.rank)) D.host.E)
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E) (δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (hg1 : (matHom (dblSp V) γ).1 = g.1.map (incA D)) (hγi : (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D))
    (hδ₀ : (matHom V δ).1 = δ₀.map (incA D)) :
    (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 = (g.1 * blkMat finSumFinEquiv δ₀ 1 * γi).map (incA D) := by
  have h1 : (matHom (dblSp V) (io V (δ, 1))).1 = blkMat finSumFinEquiv (matHom V δ).1 1 := by
    rw [matHom_io, val_blkGL]
    simp
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, h1, hg1, hγi, hδ₀, Matrix.map_mul, Matrix.map_mul,
    blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem isoFrame_keep : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → ∃ y, x = K *ᵥ y) → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∃ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G ∧ δ₀ * (leviMat finSumFinEquiv γi * K) = leviMat finSumFinEquiv γi * K * G := by
  intro D V γ hγ γi hγi r K hK hKsurj hC δ hδ δ₀ hδ₀ hsieg
  have inj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, -, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  obtain ⟨d, -, hd1, -⟩ := exists_rat V hδ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective inj (hγi.symm.trans hg2)
  have hδ₀' : δ₀ = d.1 := Matrix.map_injective inj (hδ₀.symm.trans hd1)
  have hgi0 : γi * g.1 = 1 := by rw [hγi']; exact g.inv_mul
  obtain ⟨X, hX⟩ : ∃ X, X = g.1 * blkMat finSumFinEquiv δ₀ 1 * γi := ⟨_, rfl⟩
  have hXmap := matHom_conj_io D V γ δ g γi δ₀ hg1 hγi hδ₀
  rw [← hX] at hXmap
  have hKX : KeepsDiag finSumFinEquiv X := by
    have h : KeepsDiag finSumFinEquiv (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 := mem_siegelOf.1 hsieg
    rw [hXmap] at h
    refine (keepsDiag_iff finSumFinEquiv).2 fun i j => inj ?_
    simpa using (keepsDiag_iff finSumFinEquiv).1 h i j
  obtain ⟨C, hCdef⟩ : ∃ C, C = leviMat finSumFinEquiv γi * K := ⟨_, rfl⟩
  rw [← hCdef] at hC ⊢
  have key : ∀ v : Fin r → D.host.E, ∃ w, δ₀ *ᵥ (C *ᵥ v) = C *ᵥ w := by
    intro v
    have h1 : γi *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) = pairVec finSumFinEquiv (C *ᵥ v) 0 := by
      rw [mulVec_pairVec_diag, mulVec_mulVec (M := diagSnd γi), hK, zero_mulVec, mulVec_mulVec, hCdef]
    have h2 : X *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) =
        g.1 *ᵥ pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 := by
      rw [hX, ← mulVec_mulVec, ← mulVec_mulVec, h1, blkMat_mulVec, mulVec_zero]
    have h3 : pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 =
        γi *ᵥ pairVec finSumFinEquiv (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      rw [← hKX.mulVec_diag, h2, mulVec_mulVec (M := γi), hgi0, one_mulVec]
    rw [mulVec_pairVec_diag] at h3
    have h4a : δ₀ *ᵥ (C *ᵥ v) = leviMat finSumFinEquiv γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inl i))
      rw [pairVec_inl, pairVec_inl] at this
      exact this
    have h4b : diagSnd γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) = 0 := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inr i))
      rw [pairVec_inr, pairVec_inr] at this
      exact this.symm
    obtain ⟨w, hw⟩ := hKsurj _ h4b
    exact ⟨w, by rw [h4a, hw, mulVec_mulVec, hCdef]⟩
  choose w hw using fun j => key (Pi.single j 1)
  have hCG : δ₀ * C = C * Matrix.of fun i j => w j i := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hw j) i
    rw [mulVec_mulVec, mulVec_single_one] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct, transpose_apply] using this
  refine ⟨Matrix.of fun i j => w j i, ?_, hCG⟩
  rw [← mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : (Matrix.of fun i j => w j i) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have h5 : C *ᵥ (a - b) = 0 := by
    have h6 : δ₀ *ᵥ (C *ᵥ (a - b)) = 0 := by rw [mulVec_mulVec, hCG, ← mulVec_mulVec, h0, mulVec_zero]
    have h7 := congrArg (fun x => (d⁻¹).1 *ᵥ x) h6
    simp only [hδ₀', mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, mulVec_zero] at h7
    exact h7
  obtain ⟨-, hli, -⟩ := hC
  have h8 := Fintype.linearIndependent_iff.1 hli (a - b) (by
    funext i
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using congrFun h5 i)
  exact sub_eq_zero.1 (funext h8)

end GlobalTheory.Core.Rk.Dich
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

def stkRows {R : Type} {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) R) : Matrix (Fin (a + a)) (Fin k) R :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem stkRows_mul {R : Type} [CommRing R] {a k l : ℕ} (X Y : Matrix (Fin a) (Fin k) R) (B : Matrix (Fin k) (Fin l) R) :
    stkRows X Y * B = stkRows (X * B) (Y * B) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [stkRows, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp [Matrix.mul_apply]

theorem keepsDiag_mul_stkRows {R : Type} [CommRing R] {n k : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    (h : KeepsDiag finSumFinEquiv M) (X : Matrix (Fin n) (Fin k) R) :
    M * stkRows X X = stkRows (leviMat finSumFinEquiv M * X) (leviMat finSumFinEquiv M * X) := by
  have hk := (keepsDiag_iff finSumFinEquiv).1 h
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Matrix.mul_apply, stkRows, Matrix.submatrix_apply, id]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  rw [← Finset.sum_add_distrib]
  rcases s with a | a
  · simp only [Matrix.fromRows_apply_inl, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, add_mul]
  · simp only [Matrix.fromRows_apply_inr, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, ← add_mul, ← hk]

theorem rat_stackRows {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) D.host.E) :
    rat (stackRows X Y) = stkRows (rat X) (rat Y) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [rat, stackRows, stkRows, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp

theorem dblDec_jX (A : HSp D) : (dblDec A).jX = stkRows (giA A) (giA A) := rat_stackRows _ _

theorem siegel_mt_jX (A : HSp D) {g : GA D (dblSp A)} (hg : g ∈ siegel A) :
    mt (dblSp A) g ⬝ (dblDec A).jX =
      (dblDec A).jX ⬝ (gA A ⬝ leviMat finSumFinEquiv (mt (dblSp A) g) ⬝ giA A) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp A) g) := mem_siegelOf.1 hg
  rw [dblDec_jX, keepsDiag_mul_stkRows hk, stkRows_mul]
  simp only [← Matrix.mul_assoc, giA_mul_gA, Matrix.one_mul]



theorem siegel_eq_levi_nC : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank),
    (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  intro D A p
  obtain ⟨p, hp⟩ := p
  obtain ⟨α, hα⟩ : ∃ α : Mx D A.rank A.rank, mt (dblSp A) p ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α := ⟨_, siegel_mt_jX A hp⟩
  obtain ⟨α', hα'⟩ : ∃ α' : Mx D A.rank A.rank, mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α' :=
    ⟨_, siegel_mt_jX A (inv_mem hp)⟩
  have e1 : α ⬝ α' = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α ⬝ α') := by
      calc (dblDec A).jX = mt (dblSp A) (p * p⁻¹) ⬝ (dblDec A).jX := by
            rw [mul_inv_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p ⬝ (mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α ⬝ α') := by rw [hα', ← Matrix.mul_assoc, hα, Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have e2 : α' ⬝ α = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α' ⬝ α) := by
      calc (dblDec A).jX = mt (dblSp A) (p⁻¹ * p) ⬝ (dblDec A).jX := by
            rw [inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p⁻¹ ⬝ (mt (dblSp A) p ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α' ⬝ α) := by rw [hα, ← Matrix.mul_assoc, hα', Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have u := GlobalTheory.MixModel.mt_unitary (dblSp A) p

  have h1 : adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 1 := by
    calc adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (mt (dblSp A) p ⬝ (dblDec A).jX) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) := by
          rw [hα, (dblDec A).pY_eq, adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (dblDec A).jX ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [u, (dblDec A).gram_XY]
  have hG : adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 0 := by
    calc adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (dblDec A).jY ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [u, (dblDec A).gram_YY]
  generalize hYdef : mt (dblSp A) p ⬝ (dblDec A).jY = Y at h1 hG
  have hpY : (dblDec A).pY ⬝ Y = adj α' := by
    calc (dblDec A).pY ⬝ Y = (adj α' ⬝ adj α) ⬝ ((dblDec A).pY ⬝ Y) := by
          rw [← adj_mul, e1, adj_one, Matrix.one_mul]
      _ = adj α' := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h0 : (dblDec A).j0 ⬝ (dblDec A).p0 = 0 :=
    Matrix.ext fun i j => by rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  generalize hu : (dblDec A).pX ⬝ Y = w
  have hY : Y = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
    calc Y = ((dblDec A).jX ⬝ (dblDec A).pX + (dblDec A).j0 ⬝ (dblDec A).p0 + (dblDec A).jY ⬝ (dblDec A).pY) ⬝ Y := by
          rw [(dblDec A).sum_eq_one, Matrix.one_mul]
      _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
          rw [h0, add_zero, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hpY, hu, add_comm]
  have hskew : adj (α' ⬝ w) = -(α' ⬝ w) := by
    rw [hY] at hG
    simp only [adj_add, adj_mul, adj_adj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₃ (dblDec A).gram_YY, cancel₃ (dblDec A).gram_YX, cancel₃ (dblDec A).gram_XY, cancel₃ (dblDec A).gram_XX,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero] at hG
    rw [adj_mul, eq_neg_iff_add_eq_zero]
    exact hG
  let a : GL (Fin A.rank) (AE D) := ⟨α, α', e1, e2⟩
  refine ⟨a, ⟨α' ⬝ w, mem_skewA.2 hskew⟩, (dblDec A).ga_ext ?_ ?_ ?_⟩
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jX, (dblDec A).levi_jX, hα]
  · exact Matrix.ext fun _ j => Fin.elim0 j
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jY, Matrix.mul_add, (dblDec A).levi_jY,
      ← Matrix.mul_assoc, (dblDec A).levi_jX, hYdef, hY]
    show _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ α ⬝ (α' ⬝ w)
    rw [Matrix.mul_assoc (dblDec A).jX, ← Matrix.mul_assoc α, e1, Matrix.one_mul]

end GlobalTheory.Core.Rk.SWLaw
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RootKeep

open GlobalTheory.IwaPlace

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem conj_mem_idAt {v : Pl D} {r : AE D} (hr : r ∈ idAt D (· = v)) : cA D r ∈ idAt D (· = v) := by
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  rw [← hact r hr, RingHom.map_mul, hc]
  exact Ideal.mul_mem_right _ _ hε.1

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (a b : AE D) :
    colMul x l (a + b) = colMul x l a + colMul x l b := by
  funext k; exact add_mul _ _ _

theorem colMul_neg {m n : ℕ} (x : Mx D m n) (l : Fin n) (a : AE D) : colMul x l (-a) = -colMul x l a := by
  funext k; exact neg_mul _ _

theorem hermAt_colMul_jY (d : HypDec S S₀ ρ) (l : Fin ρ) (b : AE D) (x : Fin S.rank → AE D) :
    hermAt S (colMul d.jY l b) x = b * cA D ((d.pX *ᵥ x) l) := by
  have hg : ∀ k m, cA D (gA S k m) = gA S m k := fun k m => congrFun (congrFun (adj_gA S) m) k
  have hp : ∀ m, cA D (d.pX l m) = ∑ k, gA S m k * d.jY k l := fun m => by

    rw [d.pX_eq, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, hg, mul_comm]
    exact congrArg _ (congrFun (congrFun (adj_adj d.jY) k) l)
  unfold hermAt colMul

  rw [Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [RingHom.map_mul, hp, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pX_colMul_jX (d : HypDec S S₀ ρ) (l : Fin ρ) (a : AE D) : (d.pX *ᵥ colMul d.jX l a) l = a := by
  have h : (d.pX * d.jX) l l = 1 := by rw [d.pX_jX, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h
  refine Eq.trans ?_ (mul_one a)
  rw [Matrix.mulVec, dotProduct, ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold colMul
  ring

theorem transv_mulVec (i j : Fin ρ) (r : AE D) (u : Fin ρ → AE D) (l : Fin ρ) :
    (transvection i j r *ᵥ u) l = u l + if l = i then r * u j else 0 := by
  rw [transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply, Function.update_apply]
  rfl

theorem adj_transv (i j : Fin ρ) (r : AE D) : adj (transvection i j r : Mx D ρ ρ) = transvection j i (cA D r) := by
  rw [transvection, transvection, adj_add, adj_one]
  congr 1
  funext a b
  change cA D (Matrix.single i j r b a) = _
  simp only [Matrix.single_apply]
  by_cases h : i = b ∧ j = a
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), RingHom.map_zero]

theorem levi_maps (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D} (hL : IsSelfDualC S L)
    (hM : MonoAt d L L₀ v) {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (h : ∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) *ᵥ y ∈ latV S L (· = v) := by
  obtain ⟨hs, -, hd⟩ := LocSD.isSDAt_latV D S L v hL
  have hX : ∀ x ∈ latV S L (· = v), colMul d.jX i (r * (d.pX *ᵥ x) j) ∈ latV S L (· = v) := fun x hx =>
    h _ (mulVec_mem_idAt _ (hs x hx) j) (((hM x).1 hx).1 j)
  obtain ⟨h1, h2, h3⟩ := (hM y).1 hy
  refine (hM _).2 ⟨fun l => ?_, fun l => ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jX l ((transvection i j r *ᵥ _) l) ∈ _
    rw [transv_mulVec, colMul_add]
    refine add_mem (h1 l) ?_
    split_ifs with hl
    · rw [hl]; exact hX y hy
    · have : colMul d.jX l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jY l ((adj (transvection i j (-r) : Mx D ρ ρ) *ᵥ _) l) ∈ _
    rw [adj_transv, transv_mulVec, colMul_add]
    refine add_mem (h2 l) ?_
    split_ifs with hl
    · rw [hl, RingHom.map_neg, neg_mul, colMul_neg]
      refine neg_mem ((hd _ fun k => ?_).2 fun x hx => ?_)
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (hs y hy) i))
      · have h4 := (hd _ (hs _ (h2 i))).1 (h2 i) _ (hX x hx)
        rw [hermAt_colMul_jY, pX_colMul_jX, RingHom.map_mul] at h4
        rw [hermAt_colMul_jY]
        convert h4 using 1
        ring
    · have : colMul d.jY l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rwa [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]

theorem levi_mem_grpAt (d : HypDec S S₀ ρ) {v : Pl D} {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (hr : r ∈ idAt D (· = v)) : d.levi (GlobalTheory.GLGen.transvGL hij r) ∈ grpAt S (· = v) := by
  refine (mem_congGrp_iff S _ _).2 fun a b => ?_
  have e : mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) - 1 =
      d.jX * (Matrix.single i j r : Mx D ρ ρ) * d.pX + d.jY * (Matrix.single j i (cA D (-r)) : Mx D ρ ρ) * d.pY := by
    rw [d.mt_levi, ← d.sum_eq_one]
    change d.jX * (transvection i j r : Mx D ρ ρ) * d.pX + _ + d.jY * adj (transvection i j (-r) : Mx D ρ ρ) * d.pY - _ = _
    rw [adj_transv, transvection, transvection]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    abel
  have k : ∀ (A : Mx D S.rank ρ) (B : Mx D ρ S.rank) (p q : Fin ρ) (s : AE D), s ∈ idAt D (· = v) →
      (A * (Matrix.single p q s : Mx D ρ ρ) * B) a b ∈ idAt D (· = v) := fun A B p q s hs => by
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.single_apply]
    split_ifs
    · exact hs
    · exact zero_mem _
  rw [← Matrix.sub_apply, e, Matrix.add_apply]
  exact add_mem (k _ _ _ _ _ hr) (k _ _ _ _ _ (conj_mem_idAt (neg_mem hr)))

theorem inK_levi_transv : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  intro D S S₀ ρ d L L₀ v hL hM i j hij r hr h
  refine ⟨levi_mem_grpAt d hij hr, fun y _ => ⟨fun hy => levi_maps d hL hM hij h hy, fun hy => ?_⟩⟩
  have h' := levi_maps d hL hM hij (r := -r) (fun a ha hb => by
    rw [neg_mul, colMul_neg]; exact neg_mem (h a ha hb)) hy
  have e : GlobalTheory.GLGen.transvGL hij (-r) = (GlobalTheory.GLGen.transvGL hij r)⁻¹ := Units.ext rfl
  rwa [Matrix.mulVec_mulVec, ← mt_mul, ← map_mul, e, inv_mul_cancel, map_one, mt_one, Matrix.one_mulVec] at h'

end GlobalTheory.FinPl.RootKeep

end
end
