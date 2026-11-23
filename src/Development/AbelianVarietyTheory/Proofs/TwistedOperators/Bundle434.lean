module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle387
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle397
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle398
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.Defs.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle399
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ThetaEigen

variable {D : D7}

def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext x; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem heisLin_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisLin ψ S T w f = heisO ψ S T w f := rfl

theorem heisO_smul_comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (k : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (k • f) = k • heisO ψ S T w f := (heisLin ψ S T w).map_smul k f

theorem addChar_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := AddChar.map_zero_eq_one ψ
  rw [← add_neg_cancel a, AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem eq_zero_of_heisO_eq_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ)
    (h : heisO ψ S T w g = 0) : g = 0 := by
  funext x
  have h1 := congrFun h (x - w)
  simp only [heisO, sub_add_cancel, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left (addChar_ne_zero ψ _)

theorem heisO_eigen_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (w : WO S T) (c : ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ x : WO S T, IsHalf e x → symplO S T w x = 0) → (∀ y : WO S T, IsHalf (cA D e) y → symplO S T w y = 0) → heisO ψ S T w f₀ = c • f₀ → ∃ c' : ℂ, heisO ψ S T w f = c' • f := by
  intro D ψ S T e Λ f₀ Φ f w c hθ hx hy hc
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hθ
  have hψ0 : ψ 0 = 1 := AddChar.map_zero_eq_one ψ
  have key : ∀ k : ℂ, k • heisO ψ S T w f₀ = f₀ → f = k • heisO ψ S T w f := by
    intro k hk
    have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ (k • (heisLin ψ S T w ∘ₗ T₀)) := by
      refine ⟨fun Φ' hΦ' x hxe => ?_, fun Φ' hΦ' y hye => ?_, ?_⟩
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.trans Φ' hΦ' x hxe, GlobalTheory.Asc.heisO_comm, hx x hxe, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.modul Φ' hΦ' y hye, GlobalTheory.Asc.heisO_comm, hy y hye, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.vac, hk]
    have h2 : f = (k • (heisLin ψ S T w ∘ₗ T₀)) Φ := hall _ hT'
    have h3 : f = T₀ Φ := hall T₀ hT₀
    rw [show (k • (heisLin ψ S T w ∘ₗ T₀)) Φ = k • heisO ψ S T w (T₀ Φ) from rfl, ← h3] at h2
    exact h2
  by_cases hc0 : c = 0
  · subst hc0
    rw [zero_smul] at hc
    have hf₀ := eq_zero_of_heisO_eq_zero ψ S T w f₀ hc
    have h1 := key 1 (by rw [one_smul, hc, hf₀])
    exact ⟨1, by rw [one_smul]; rw [one_smul] at h1; exact h1.symm⟩
  · refine ⟨c, ?_⟩
    have h1 := key c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
    calc heisO ψ S T w f = c • (c⁻¹ • heisO ψ S T w f) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      _ = c • f := by rw [← h1]

end GlobalTheory.ThetaEigen
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  first | exact @GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | exact GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | (intros; apply GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct


theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_ext_localComponents : ∀ {D : D7} (V : HSp D) (x y : GfC V), (∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V (x : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V (y : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u)) → x = y := by
  first | exact @GlobalTheory.TrFinExt.gfc_ext | exact GlobalTheory.TrFinExt.gfc_ext | (intros; apply GlobalTheory.TrFinExt.gfc_ext <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.DSFlip

variable {n : ℕ} (ε : Fin n → Bool)

theorem jm_not : Formalism.REAL.Jm (fun a => !ε a) = -Formalism.REAL.Jm ε := by
  ext a b
  by_cases hab : a = b
  · subst hab; cases h : ε a <;> simp [Formalism.REAL.Jm, h]
  · simp [Formalism.REAL.Jm, hab]

theorem inUJ_not (g : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.inUJ (fun a => !ε a) g ↔ Formalism.REAL.inUJ ε g := by
  unfold Formalism.REAL.inUJ
  rw [jm_not, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem uJset_not : Formalism.MainNotions.S.UJset (fun a => !ε a) = Formalism.MainNotions.S.UJset ε :=
  Set.ext fun g => inUJ_not ε g

theorem kset_not : Formalism.REAL.Kset (fun a => !ε a) = Formalism.REAL.Kset ε := by
  ext g
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq, jm_not, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_not : Formalism.REAL.rhoC (fun a => !ε a) = Formalism.REAL.rhoC ε := by
  funext a; simp [Formalism.REAL.rhoC]

theorem rhoN_not : Formalism.REAL.rhoN (fun a => !ε a) = Formalism.REAL.rhoN ε := by
  funext a; simp [Formalism.REAL.rhoN]

theorem lowK_not (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK (fun a => !ε a) lam = Formalism.QuantumDeterminants.lowK ε lam := by
  simp only [Formalism.QuantumDeterminants.lowK, rhoC_not, rhoN_not]

theorem vNormSq_not (μ : Fin n → ℝ) : Formalism.MainNotions.S.vNormSq (fun a => !ε a) μ = Formalism.MainNotions.S.vNormSq ε μ := by
  simp only [Formalism.MainNotions.S.vNormSq, rhoC_not]

theorem cDom_not (μ Λ : Fin n → ℝ) : Formalism.MainNotions.S.CDom (fun a => !ε a) μ Λ ↔ Formalism.MainNotions.S.CDom ε μ Λ := by
  simp [Formalism.MainNotions.S.CDom]

theorem isKTypeOf_not {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf (fun a => !ε a) σ Λ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  simp only [Formalism.MainNotions.S.IsKTypeOf, Formalism.MainNotions.S.IsKStableOn, kset_not, cDom_not]

def flipU : Formalism.REAL.UJ (fun a => !ε a) ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨g.1, (inUJ_not ε _).1 g.2⟩
  invFun g := ⟨g.1, (inUJ_not ε _).2 g.2⟩
  left_inv g := rfl
  right_inv g := rfl
  map_mul' g h := rfl

theorem flipU_cont : Continuous (flipU ε) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem flipU_symm_cont : Continuous (flipU ε).symm :=
  Continuous.subtype_mk continuous_subtype_val _

theorem memLp_flip {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ flipU ε) 2 (Formalism.REAL.muG (fun a => !ε a)) := by
  haveI : ((Formalism.REAL.muG (fun a => !ε a)).map (flipU ε)).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ (flipU ε) (flipU_cont ε) (flipU_symm_cont ε)
  refine MemLp.comp_of_map ?_ (flipU_cont ε).measurable.aemeasurable
  rw [Measure.isMulLeftInvariant_eq_smul ((Formalism.REAL.muG (fun a => !ε a)).map (flipU ε)) (Formalism.REAL.muG ε)]
  exact hF.smul_measure ENNReal.coe_ne_top

theorem flipU_apply (g : Formalism.REAL.UJ (fun a => !ε a)) :
    ((flipU ε g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) := rfl

theorem coefOn_flip {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H) :
    Formalism.MainNotions.S.coefOn (ε := fun a => !ε a) σ v w = Formalism.MainNotions.S.coefOn (ε := ε) σ v w ∘ flipU ε := by
  funext g
  simp only [Function.comp_apply, Formalism.MainNotions.S.coefOn, Formalism.MainNotions.S.umat, flipU_apply]

end GlobalTheory.DSFlip

theorem GlobalTheory.PairLift.isDS_flip : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  intro n H _ _ ε lam σ ⟨hc, hn, hu, hi, hsq, ⟨S, hS⟩, hmin⟩
  refine ⟨hc, hn, ?_, ?_, ?_, ⟨S, ?_⟩, ?_⟩
  · rw [GlobalTheory.DSFlip.uJset_not]; exact hu
  · rw [GlobalTheory.DSFlip.uJset_not]; exact hi
  · intro v w
    rw [GlobalTheory.DSFlip.coefOn_flip]
    exact GlobalTheory.DSFlip.memLp_flip ε (hsq v w)
  · rw [GlobalTheory.DSFlip.isKTypeOf_not, GlobalTheory.DSFlip.lowK_not]; exact hS
  · intro μ S' hS'
    rw [GlobalTheory.DSFlip.lowK_not, GlobalTheory.DSFlip.vNormSq_not, GlobalTheory.DSFlip.vNormSq_not]
    exact hmin μ S' ((GlobalTheory.DSFlip.isKTypeOf_not ε σ μ S').1 hS')

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowDatum

private theorem prod_apply_update_eq_mul_prod_erase {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (F : ∀ i, X i → ℂ) (x : ∀ i, X i) (j : ι) (y : X j) :
    ∏ i, F i (Function.update x j y i) = F j y * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private theorem sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (s : Finset ι) :
    ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert j s hj ih =>
    intro x

    have hg : (∑ d ∈ S, (c d * ∏ i ∈ Finset.univ.erase j,
        (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i)) • Φ d j) = 0 := by
      funext y
      rw [Finset.sum_apply, Pi.zero_apply, ← ih (Function.update x j y)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [prod_apply_update_eq_mul_prod_erase (fun i => if i ∈ s then Tm i (Φ d i) else Φ d i) x j y]
      simp only [Pi.smul_apply, smul_eq_mul, if_neg hj]
      ring

    have hT := congrArg (fun g => Tm j g (x j)) hg

    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hT
    rw [← hT]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have h2 : ∏ i ∈ Finset.univ.erase j, (if i ∈ insert j s then Tm i (Φ d i) else Φ d i) (x i) =
        ∏ i ∈ Finset.univ.erase j, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [Finset.mem_insert, hij, false_or]
    rw [h2, if_pos (Finset.mem_insert_self j s)]
    ring

theorem sum_prod_map_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (x : ∀ i, X i) :
    ∑ d ∈ S, c d * ∏ i, Tm i (Φ d i) (x i) = 0 := by
  have := sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero Tm S c Φ h Finset.univ x
  simpa using this

theorem sum_prod_map_eq_zero₂ {κ : Type} {m : ℕ} {X Y : Fin m → Type} (TX : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ))
    (TY : ∀ i, (Y i → ℂ) →ₗ[ℂ] (Y i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ j, X j → ℂ) (Ψ : κ → ∀ i, Y i → ℂ)
    (h : ∀ (x : ∀ j, X j) (y : ∀ i, Y i), ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ d i (y i) = 0)
    (x : ∀ j, X j) (y : ∀ i, Y i) :
    ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) = 0 := by

  have hx : ∀ (y : ∀ i, Y i) (x : ∀ j, X j),
      ∑ d ∈ S, (c d * ∏ i, Ψ d i (y i)) * ∏ j, TX j (Φ d j) (x j) = 0 := by
    intro y
    refine sum_prod_map_eq_zero TX S (fun d => c d * ∏ i, Ψ d i (y i)) Φ (fun x => ?_)
    rw [← h x y]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

  have hy := sum_prod_map_eq_zero TY S (fun d => c d * ∏ j, TX j (Φ d j) (x j)) Ψ (fun y' => by
    rw [← hx y' x]
    exact Finset.sum_congr rfl fun d _ => by ring) y
  rw [← hy]


end GlobalTheory.FirstRowDatum

end
end

section

open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem schwartz_tendsto_apply_of_tendsto_pointwise :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  intro V _ _ _ S hS g g₀ hg
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have hq := schwartz_withSeminorms ℂ V ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n)) := by
    refine hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_
    intro k f
    exact ((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range
  have hE := hUE.equicontinuous g₀
  have h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ)) := by
    intro U hU
    have := (hg.comp hu).eventually (hE U hU)
    rw [Filter.mem_map]
    exact this.mono fun n hn => hn n
  exact ((hS g₀).comp hu).congr_uniformity h1

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.squareFlip_rows_integralGL_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ u ∈ KO k A, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      (ν (gdet u) : ℂ) * squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ
          (fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂)) =
        squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ X := by
  first | exact @GlobalTheory.SquareFlipRows.squareFlip_one_rows | exact GlobalTheory.SquareFlipRows.squareFlip_one_rows | (intros; apply GlobalTheory.SquareFlipRows.squareFlip_one_rows <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

theorem _root_.GlobalTheory.T.exists_finsetSum_translates_fixed_compactSubgroup : ∀ {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) (K : Subgroup G), IsCompact (K : Set G) → ∀ x : X, IsOpen {g | ρ g x = x} → ∃ s : Finset G, (∀ g ∈ s, g ∈ K) ∧ s.Nonempty ∧ ∀ k ∈ K, ρ k (∑ g ∈ s, ρ g x) = ∑ g ∈ s, ρ g x := by
  first | exact @GlobalTheory.exists_finset_sum_translate_fixed | exact GlobalTheory.exists_finset_sum_translate_fixed | (intros; apply GlobalTheory.exists_finset_sum_translate_fixed <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.exists_inequivalentRepresentatives_through_member : ∀ (G : Type) [Group G] [TopologicalSpace G] (m : ℕ) (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), ∀ i₀ : Fin m, ∃ (n : ℕ) (s : Fin n → Fin m), (∀ i j, i ≠ j → IsEmpty ((σ (s i)).Equiv (σ (s j)))) ∧ (∃ j, s j = i₀) ∧ ∀ i, ∃ j, Nonempty ((σ i).Equiv (σ (s j))) := by
  first | exact @GlobalTheory.TrUnion.exists_reps_through | exact GlobalTheory.TrUnion.exists_reps_through | (intros; apply GlobalTheory.TrUnion.exists_reps_through <;> assumption)
end
