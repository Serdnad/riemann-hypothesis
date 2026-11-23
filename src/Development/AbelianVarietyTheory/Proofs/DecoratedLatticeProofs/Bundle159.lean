module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle138
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S (GlobalTheory.ChiGrid.negSp T) χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om) ∧ IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource om) := by
  first | exact @GlobalTheory.ConjWeil.conj_isWeilDatumO | exact GlobalTheory.ConjWeil.conj_isWeilDatumO | (intros; apply GlobalTheory.ConjWeil.conj_isWeilDatumO <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

theorem _root_.GlobalTheory.T.gluedLatticeDatum_mainPart_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n') (Q : Pair k n), mainDatum q χ ε P Q ∈ SB (Matrix n n' k) := by
  first | exact @GlobalTheory.FinPl.Comm.mainDatum_mem_SB | exact GlobalTheory.FinPl.Comm.mainDatum_mem_SB | (intros; apply GlobalTheory.FinPl.Comm.mainDatum_mem_SB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuotFundDom

theorem volQ_and_integrable_iff : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν = (ν X).toReal ∧ ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → (Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F) (GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) ↔ IntegrableOn F X ν) := by
  intro D V ν X hν hX
  refine ⟨?_, fun F hF _ => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, Measure.real, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hX]
  · have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
    rw [← memLp_one_iff_integrable, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hX, hL.lift_descend,
      memLp_one_iff_integrable]
    rfl

end GlobalTheory.QuotFundDom
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.IwSplit

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (bc stabGL GLint cT)

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

def shear : GL ι A :=
  ⟨(Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 0 (-1) 1).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp⟩

theorem shear_mulVec (x y : m → A) : (shear e).1 *ᵥ pairVec e x y = pairVec e x (x + y) := by
  simp [mulVec_pairVec, shear]

theorem bc_shear {B : Type} [CommRing B] (f : A →+* B) : bc f (shear e) = shear e :=
  Units.ext (by
    change ((Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm).map f =
      (Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map])

omit [DecidableEq m] [DecidableEq ι] in
theorem pair_dblGram (J : Matrix m m A) (x y x' y' : m → A) :
    pairVec e x y ⬝ᵥ dblGram e J *ᵥ pairVec e x' y' = x ⬝ᵥ J *ᵥ x' - y ⬝ᵥ J *ᵥ y' := by
  rw [dblGram, blkMat_mulVec, Matrix.neg_mulVec]
  simp [dotProduct, ← e.sum_comp, sub_eq_add_neg]

theorem keepsDiag_of_pairing {J : Matrix m m A} (hJ : IsUnit J.det) {x : Matrix ι ι A} {y : GL ι A}
    (h : ∀ u' u, (x *ᵥ u') ⬝ᵥ dblGram e J *ᵥ (y.1 *ᵥ u) = u' ⬝ᵥ dblGram e J *ᵥ u) (hy : y ∈ stabGL (diagSub A e)) :
    KeepsDiag e x := by
  refine keepsDiag_of_mulVec fun w hw => ?_
  obtain ⟨a, rfl⟩ := (mem_diagSub e).1 hw
  obtain ⟨s, t, hst⟩ : ∃ s t, x *ᵥ pairVec e a a = pairVec e s t := ⟨_, _, (pairVec_eta e _).symm⟩
  rw [hst, pairVec_mem_diagSub, ← sub_eq_zero]
  have h1 : ∀ b, (s - t) ⬝ᵥ J *ᵥ b = 0 := fun b => by
    obtain ⟨c, hc⟩ := (mem_diagSub e).1 ((inv_mem hy (pairVec e b b)).1 ((pairVec_mem_diagSub e).2 rfl))
    have h2 := h (pairVec e a a) ((y⁻¹).1 *ᵥ pairVec e b b)
    rw [Matrix.mulVec_mulVec _ y.1, Units.mul_inv, Matrix.one_mulVec, hst, hc, pair_dblGram, pair_dblGram,
      sub_self] at h2
    rw [sub_dotProduct, h2]
  funext i
  have h3 := h1 (J⁻¹ *ᵥ Pi.single i 1)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec, dotProduct_single, mul_one] at h3

end Pure

theorem iwasawa_diag {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {n : ℕ} (x : GL (Fin (n + n)) K) : ∃ k : GL (Fin (n + n)) V,
    x * bc (algebraMap V K) k ∈ stabGL (diagSub K (finSumFinEquiv (m := n) (n := n))) := by
  obtain ⟨k, b, hb, h⟩ := GlobalTheory.ValIwasawa.iwasawa V K (n + n) (x⁻¹ * shear finSumFinEquiv)
  refine ⟨k * (shear finSumFinEquiv)⁻¹, inv_mem_iff.1 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => ?_))⟩
  obtain ⟨a, rfl⟩ := (mem_diagSub _).1 hw
  have h1 : (x * bc (algebraMap V K) (k * (shear finSumFinEquiv)⁻¹))⁻¹ * shear finSumFinEquiv =
      shear finSumFinEquiv * b := by
    rw [map_mul, map_inv, bc_shear, mul_inv_rev, mul_assoc, h, mul_inv_rev, inv_inv, mul_assoc]
    exact congrArg _ (inv_mul_cancel_left _ _)
  have h2 : (b.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    refine hb ?_
    change (Fin.castAdd n j : ℕ) < Fin.natAdd n i
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : pairVec finSumFinEquiv a a = (shear finSumFinEquiv).1 *ᵥ pairVec finSumFinEquiv a 0 := by
    rw [shear_mulVec, add_zero]
  rw [h3, Matrix.mulVec_mulVec, ← Units.val_mul, h1, Units.val_mul, ← Matrix.mulVec_mulVec,
    mulVec_pairVec _ b.1, h2, shear_mulVec, pairVec_mem_diagSub]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_siegelH_of_split (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) {g : GLoc σ Q v} (hg : splitHom σ Q τ g ∈ stabGL (diagSub (Fv F v) finSumFinEquiv)) :
    g ∈ siegelH (Fv F v) σ Q := by
  have e : Q.map τ = dblGram finSumFinEquiv (J.map τ) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), dblGram, Matrix.map_neg _ (map_neg _)]
  have hu : IsUnit (J.map τ).det := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact ((map_ne_zero τ).2 hJ).isUnit
  have h1 := (keepsDiag_iff _).1 (mem_stabGL_diagSub.1 hg)
  have h2 := (keepsDiag_iff _).1 (keepsDiag_of_pairing finSumFinEquiv hu (x := (splitHom σ Q (τ.comp σ) g).1)
    (fun u' u => e ▸ pairing_splitHom τ g u' u) hg)
  refine mem_siegelOf.2 ((keepsDiag_iff _).2 fun i j => split_ext h τ ?_ ?_)
  · rw [map_add (f := _), map_add (f := _)]; exact h1 i j
  · rw [map_add (f := _), map_add (f := _)]; exact h2 i j

theorem hasIwasawa_of_algHom (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : IsHermND σ J)
    (hQ' : IsHermND σ Q) (τ : E →ₐ[F] Fv F v) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hβ := (isLatticeFrame_dbl ha).isSplitBasis τ h
  rw [bc_blkGL, bc_blkGL] at hβ
  generalize bc (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (bc (compFin F E v) a) = β at hβ
  have hd : blkGL finSumFinEquiv (β, β) ∈ stabGL (diagSub (Fv F v) finSumFinEquiv) :=
    mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)
  obtain ⟨k, hk⟩ := iwasawa_diag (V := v.adicCompletionIntegers F) (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β)) g)
  obtain ⟨κ, hκ⟩ := (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β))).surjective
    (bc (algebraMap (v.adicCompletionIntegers F) (Fv F v)) k)
  have h1 : κ ∈ KFin σ Q L v :=
    (mem_stabLoc_iff_GLint h hQ' (isSelfDualAt_dbl hQ hL) hβ).2 (hκ ▸ ⟨k, rfl⟩)
  rw [← hκ, ← map_mul, splitEquivIn_apply] at hk
  have h2 := mul_mem (mul_mem hd hk) (inv_mem hd)
  rw [← mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right] at h2
  exact ⟨⟨g * κ, mem_siegelH_of_split h hQ hJ.2 τ h2⟩, κ⁻¹, inv_mem h1, (mul_inv_cancel_right g κ).symm⟩

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSelfDualAt_of_isSelfDualC {D : D7} {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) (v : FinPl D) :
    IsSelfDualAt D.sp.cm.sig A.gram L v :=
  (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL)).2
    (fun y => hL.2 y) v

theorem hasIwasawa_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D,
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v →
    HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  intro D A L hL v ⟨P, P', hne, hP, hP'⟩
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  exact hasIwasawa_of_algHom (isCMExt_host D) (gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
    (GlobalTheory.Doubling.isHermND_gram (dblSp A)) τ L (isSelfDualAt_of_isSelfDualC hL v)

end Record

end GlobalTheory.Core.Rk.IwSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

theorem _root_.GlobalTheory.T.fockPolynomialJetValue_eq_jetLinearForm_rescaled : ∀ (D : D7) (S T : HSp D) (s : ℂ) (cD : D.what₂.Tau → ℂ), (∀ τ, cD τ ≠ 0) → ∀ (G : VCx D.what₂.Tau S.rank T.rank → ℂ) (P : FP D.what₂.Tau S.rank T.rank), jetP S T rfl rfl s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) P) := by
  first | exact @GlobalTheory.KJInf.jetP_eq_jetL | exact GlobalTheory.KJInf.jetP_eq_jetL | (intros; apply GlobalTheory.KJInf.jetP_eq_jetL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalMatrix_of_mem_periodLattice : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧ embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := by
  first | exact @GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC | exact GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC | (intros; apply GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) N N', (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) ↔ toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  first | exact @GlobalTheory.AdForm.RatLat.finOf_mem_iff | exact GlobalTheory.AdForm.RatLat.finOf_mem_iff | (intros; apply GlobalTheory.AdForm.RatLat.finOf_mem_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ f, IsThetaFunO ψ S T f → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → xiN θ S T hS hT δ sc (heisO ψ S T v f) = Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT γ)) (xiN θ S T hS hT δ sc f) := by
  first | exact @GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf | exact GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf | (intros; apply GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.om_pureTensorO_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsHol θ S T ψ f → IsHol θ S T ψ (om (g, h) f) ∧ ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) ∧ om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (om (g, h) f) P := by
  first | exact @GlobalTheory.AdForm.FinComm.finite_comm_creation | exact GlobalTheory.AdForm.FinComm.finite_comm_creation | (intros; apply GlobalTheory.AdForm.FinComm.finite_comm_creation <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAComp
open GlobalTheory.AdForm.HalfPairing

theorem conjP_not_mem {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS) : Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro hc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  rw [GlobalTheory.OffIdemDen.conjP_eq_cP] at hc
  have hd : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ P (es P) := fun P hP =>
    GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ (GlobalTheory.IdemSupport.cP P) (cA D (es P)) := fun P hP =>
    GlobalTheory.IdemSupport.delta_conj hΦ (hd P hP)
  have h1 : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hE : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (es P') (GlobalTheory.IdemSupport.cP P) :=
      map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hE, Finset.sum_eq_single (GlobalTheory.IdemSupport.cP P) (fun P' hP' hne => (hd P' hP').2.2 _ (fun h => hne h.symm))
      (fun h => absurd hc h), (hd _ hc).2.1]
  have h2 : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hC : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (cA D (es P')) (GlobalTheory.IdemSupport.cP P) := by

      rw [map_sum]; exact map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hC, Finset.sum_eq_single P (fun P' hP' hne => (hdc P' hP').2.2 _ (fun h => hne (by
        have := congrArg GlobalTheory.IdemSupport.cP h
        rwa [GlobalTheory.OffIdemDen.cP_cP, GlobalTheory.OffIdemDen.cP_cP, eq_comm] at this)))
      (fun h => absurd hP h), (hdc P hP).2.1]
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (∑ P ∈ SS, es P) (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P)
  rw [horth, h1, h2, one_mul, GlobalTheory.IdemSupport.ev_zero] at h3
  exact one_ne_zero h3.symm

theorem halfA_smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E)) :
    (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by rw [_root_.zpow_neg, zpow_one, inv_inv, pow_zero, one_mul])
  · exact key 2 (by rw [neg_neg, zpow_one, pow_two, mul_assoc, mul_inv_cancel₀ hc', mul_one])
  · exact key 1 (by rw [neg_zero, zpow_zero, inv_one, pow_one, mul_one])

theorem halfA_mem_locP_conj {D : D7} {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.HomE D.host.E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE D.host.E a b} (hx : x ∈ halfAO SS M c) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS)
    (hP' : Formalism.L2.Col.conjPrime₂ P ∉ SS) : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := by
  have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ P)))⁻¹ • x ∈
      Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := (Submodule.mem_iInf _).1 hx _
  have hcc : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := by
    rw [GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.cP_cP]
  have he : expS SS (Formalism.L2.Col.conjPrime₂ P) = -1 := by
    unfold expS; rw [if_neg hP', if_pos (by rw [hcc]; exact hP)]
  have hc' : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [he, neg_neg, zpow_one] at h
  have := nsmul_mem h c
  rwa [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hc', one_smul] at this

theorem halfA_mem_locP_off {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ}
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)) : x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have he : expS SS Q = 0 := by
    unfold expS; rw [if_neg (fun h => hQ (Or.inl h)), if_neg (fun h => hQ (Or.inr h))]
  rwa [he, neg_zero, zpow_zero, inv_one, one_smul] at h



theorem zmem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _ x' hx
  have hA : ((LinearMap.toMatrix' x').map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
    have hE' := hE
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE'
    have e1 : ((LinearMap.toMatrix' x').map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x').map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j

      rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
      rfl
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc hN (hes PP hPP) ?_
      (halfA_mem_locP_conj hc hx hPP (conjP_not_mem hE hPP))
    exact GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => by
      rw [Finset.mem_singleton.1 hQ]; exact hes PP hPP, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
  have hcx : ((c : D.host.E) • x') ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    GlobalTheory.ThetaMove.mem_of_locP fun Q => halfA_smul_mem_locP hc hx Q
  obtain ⟨d, hd0, hdx, hdG⟩ := GlobalTheory.T.exists_denominator_avoiding_given_primes D.host.E _ _ _ (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc x' hcx
    (fun Q hQ => halfA_mem_locP_off hx Q hQ)
  obtain ⟨a₁, a₂, ha₁, ha₂, ho⟩ := GlobalTheory.T.offIdempotent_mem_ideal_two_integers D e SS hE c hc d hd0 hdG
  have hB : a₁ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₁ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hcx))
  have hC : a₂ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((d : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₂ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hdx))
  convert add_mem hA (add_mem hB hC) using 1
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hinfc := GlobalTheory.PlaceVec.infPart_cA hinf
  have i1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := fun M i j => by
    have := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
    simpa using this
  have f1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := fun M i j => by
    rw [GlobalTheory.LatVacSign.finRat_eq]; rfl
  rw [← GlobalTheory.LatVacSign.finRat_eq, ← GlobalTheory.LatVacSign.finRat_eq]
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, i1, hinf, hinfc,
      mul_zero, zero_mul, sub_zero, add_zero]
  · have hs : ∀ r : D.host.E, LinearMap.toMatrix' (r • x') i j = r * LinearMap.toMatrix' x' i j := fun r => by
      rw [map_smul]; rfl
    have ho' := congrArg (finPart D) ho
    simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_one] at ho'
    simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, f1, hs]
    linear_combination (finPart D (incA D (LinearMap.toMatrix' x' i j))) * ho'

end GlobalTheory.HalfAComp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatLatPer

open GlobalTheory.LatVac

theorem finRat_mem_latO_of_perO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x)).reindex (finCongr hT.symm) (finCongr hS.symm)) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D ψ θ S T a b hS hT δ sc hP N N' ΛS ΛT hΛS hΛT h1 h2 x hx
  subst hS hT
  have e1 : N = ΛS := (SetLike.coe_injective h1).symm
  have e2 : N' = ΛT := (SetLike.coe_injective h2).symm
  subst e1 e2
  have hr : (LinearMap.toMatrix' x).reindex (finCongr (rfl : T.rank = T.rank)) (finCongr (rfl : S.rank = S.rank)) =
      LinearMap.toMatrix' x := by
    ext i j; rfl
  rw [hr, GlobalTheory.LatVacSign.finRat_eq]
  refine GlobalTheory.LatVac.finTens_mem_latO (one_mem_intAf _) ?_
  rw [GlobalTheory.AdForm.RatLat.mem_latRat_iff_perO N' hΛS, Matrix.toLin'_toMatrix', GlobalTheory.AdForm.RatLat.AA_eq hP.cc]
  exact hx

end GlobalTheory.AdForm.RatLatPer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.halfCocycle_isotropic_idempotentHalves_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ u ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ v ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplOH S T (e • u) (cA D e • v)) = 1 := by
  first | exact @GlobalTheory.HalfCocycle.char_symplOH_idem_conj | exact GlobalTheory.HalfCocycle.char_symplOH_idem_conj | (intros; apply GlobalTheory.HalfCocycle.char_symplOH_idem_conj <;> assumption)
end
