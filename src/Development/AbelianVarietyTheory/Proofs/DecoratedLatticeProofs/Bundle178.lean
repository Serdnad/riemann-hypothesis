module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.AInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mem_intLoc_of_mapsTo {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hX : ∀ x ∈ latLoc F L v, X *ᵥ x ∈ latLoc F L v) : X.det ∈ intLoc F E v := by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  set b := Formalism.UG.bc (compFin F E v) a with hb
  set N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (b⁻¹).1 * X * b.1 with hN
  have hent : ∀ i j, N i j ∈ intLoc F E v := by
    intro i j
    have h1 : b.1 *ᵥ (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v :=
      (ha v (Pi.single j 1)).1 fun l => by
        by_cases e : l = j
        · subst e; simp
        · simp [e]
    have h2 := hX _ h1
    have hbN : b.1 * N = X * b.1 := by
      rw [hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h3 : b.1 *ᵥ (N *ᵥ Pi.single j 1) ∈ latLoc F L v := by
      rwa [Matrix.mulVec_mulVec, hbN, ← Matrix.mulVec_mulVec]
    have h4 := (ha v _).2 h3 i
    simpa using h4
  have hdet : N.det = X.det := by
    rw [hN, Matrix.det_mul, Matrix.det_mul, mul_comm ((b⁻¹).1.det * X.det), ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  let N' : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i j => ⟨N i j, hent i j⟩
  have hmap : N'.map (intLoc F E v).subtype = N := by ext i j; rfl
  have hd := RingHom.map_det (intLoc F E v).subtype N'
  rw [← hdet, ← hmap, ← RingHom.mapMatrix_apply, ← hd]
  exact (N'.det).2

theorem aH_mem_intLoc_of_lattice (σ : E →ₐ[F] E) {n : ℕ} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (p : siegelH (Fv F v) σ Q) (hp : (p : GLoc σ Q v) ∈ GlobalTheory.Doubling.KFin σ Q L v) :
    ((aH _ σ Q p : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  have hk : KeepsDiag finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := GlobalTheory.AdelicU.matHom (Fv F v) σ Q)).1 p.2
  refine det_mem_intLoc_of_mapsTo L v (leviMat finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1) fun x hx => ?_
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hp _).1 h1
  rw [hk.mulVec_diag, latLoc_sumLat, pairVec_mem_sumLat] at h2
  exact h2.1

theorem aH_mem_intLoc : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  intro D A L hL v p hp
  haveI := GlobalTheory.AdIsom.selfDual_isFullLattice hL
  exact aH_mem_intLoc_of_lattice D.sp.cm.sig (n := A.rank) (dblSp A).gram L v p hp

end GlobalTheory.Core.Rk.AInt
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
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory

theorem LSD_hasProd_LvTw : ∀ (D : D7) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle) (r : ℕ) (κ : ℝ), GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sf : Set (FinPl D))) par r κ → ∀ z : ℂ, κ + 1 < z.re → HasProd (fun v : {v : FinPl D // v ∉ (Sf : Set (FinPl D))} => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χ) v.1 z) (GlobalTheory.LFun.LSD D Sf par χ z) := by
  intro D Sf par χ r κ h z hz
  exact GlobalTheory.LFun.hasProd_Lv (h.converges_twist_val χ hz)

end GlobalTheory
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
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LFun

open GlobalTheory.Doubling GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ideleAt_eq_prod_locIdele {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) :
    ideleAt F E v x = ∏ w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset.attach,
      locIdele F w.1 (Units.map (toCompl ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2)).toMonoidHom x) := by
  classical
  have hc : ∀ u' : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u') (AlgHom.id F E)
      (finTens F E (ideleAt F E v x)) = (unitFin F E u' (ideleAt F E v x) : Fv F u' ⊗[F] E) := fun u' => by
    change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
    rw [← Algebra.TensorProduct.map_comp]
    rfl
  refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
  · rw [Units.coe_prod, map_prod]
    simp only [infTens_locIdele, Finset.prod_const_one]
    exact map_extUnit_zero (fstA F) _ _ (fun a => rfl) x
  · rw [Units.coe_prod, map_prod (finTens F E), map_prod (finAdEquiv F E)]
    simp only [finTens_locIdele]
    change _ = evalV E u (∏ w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset.attach, _)
    rw [map_prod]
    by_cases hu : u.under (𝓞 F) = v
    · rw [finAdEquiv_apply hu, hc, unitFin_ideleAt_self]
      have hm : u ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset :=
        (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 hu
      rw [Finset.prod_eq_single_of_mem ⟨u, hm⟩ (Finset.mem_attach _ _)]
      · exact (finSingle_self u _).symm
      · rintro b - hb
        exact finSingle_ne (fun e => hb (Subtype.ext e.symm)) _
    · rw [finAdEquiv_apply rfl, hc, unitFin_ideleAt_ne hu, Units.val_one, map_one]
      refine (Finset.prod_eq_one fun b _ => ?_).symm
      have hb : b.1.under (𝓞 F) = v := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 b.2
      exact finSingle_ne (fun e : u = b.1 => hu (by rw [e]; exact hb)) _

theorem charAt_eq_one_of_unrAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : (AF F ⊗[F] E)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 F)) (y : (Fv F v ⊗[F] E)ˣ)
    (hy : (y : Fv F v ⊗[F] E) ∈ intLoc F E v) (hy' : ((y⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v)
    (hμ : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt μ w) : charAt μ v y = 1 := by
  show μ (ideleAt F E v y) = 1
  rw [ideleAt_eq_prod_locIdele, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have h : w.1.under (𝓞 F) = v := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2
  have hu : Formalism.L2.Host.IsUnitAt w.1 (Units.map (toCompl h).toMonoidHom y) := by
    refine (EulerTie.isUnitAt_iff w.1 _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (InertChart.toCompl_mem h hy)
    · rw [← map_inv]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (InertChart.toCompl_mem h hy')
  have := hμ w.1 h _ hu
  exact Circle.ext (congrArg Units.val this)

end GlobalTheory.LFun

theorem GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (v : FinPl D) (y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → ((y⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → charAt μ v y = 1 := by
  intro D μ v y hy hy' hμ
  exact GlobalTheory.LFun.charAt_eq_one_of_unrAt μ v y hy hy' hμ
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
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  first | exact @GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | (intros; apply GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split <;> assumption)
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


theorem _root_.GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A) (a : GL (Fin A.rank) (AE D)), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) → (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) ((Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)) ∧ ∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  first | exact @GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl | exact GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl | (intros; apply GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl <;> assumption)
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


theorem _root_.GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D, ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  first | exact @GlobalTheory.InertIwasawa.hasIwasawa_inert | exact GlobalTheory.InertIwasawa.hasIwasawa_inert | (intros; apply GlobalTheory.InertIwasawa.hasIwasawa_inert <;> assumption)
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

noncomputable section

namespace GlobalTheory.Core.Rk.MajFrame

theorem exists_maj_cart : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  intro D θ A sA hθ hs
  obtain ⟨a, ha, -, hfs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ hs
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hfs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D A τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D A τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

end GlobalTheory.Core.Rk.MajFrame
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem hgt_one_components : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → (∀ v, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v k = 1) ∧ (∀ κ ∈ GfC V, ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w κ = 1) ∧ ∀ b ∈ GinfC V, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b = 1 := by
  intro D V Λ hΛ
  haveI : Submodule.IsFullLattice D.host.E Λ := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ
  refine ⟨fun v k hk => ?_, fun κ hκ w => ?_, fun b hb v => ?_⟩
  · have hK := (GlobalTheory.Doubling.ioH_mem_KFin (L := Λ) (GlobalTheory.Doubling.gram_hdbl V) (g := k) (g' := 1)).2 ⟨hk, one_mem _⟩
    have := GlobalTheory.Doubling.hgtH_of_mem (GlobalTheory.Doubling.continuous_absEv v) (GlobalTheory.Doubling.isCompact_KFin v) hK
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
    exact_mod_cast this
  · exact GlobalTheory.AdelicU.mem_finPts_iff_forall.1 hκ w
  · exact GlobalTheory.AdelicU.mem_infPts_iff_forall.1 hb v

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem integral_autMeasure_eq_setIntegral : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F q ∂(GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) = ∫ g in X, F g ∂ν := by
  intro D V ν X hν hX F hF _
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
  rw [GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem isCompact_of_integral_open (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (K : Subgroup (GA D V)) (hKf : K ≤ GfC V)
    (hKi : ∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K) :
    IsCompact (K : Set (GA D V)) := by
  haveI : Submodule.IsFullLattice D.host.E Λ :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ
  obtain ⟨U, hUo, hUK⟩ := hU
  have hGf : IsClosed ((GfC V : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [GlobalTheory.AdelicU.GfC_eq]; exact GlobalTheory.AdelicU.isClosed_finPts _ _

  have hopen : IsOpen ((K.subgroupOf (GfC V)) : Set (GfC V)) := by
    refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) ?_ ?_
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hx) x.2)
    · exact hUo.preimage continuous_subtype_val
  have hcl : IsClosed ((K.subgroupOf (GfC V)) : Set (GfC V)) := Subgroup.isClosed_of_isOpen _ hopen
  have hKcl : IsClosed (K : Set (GA D V)) := by
    have h := hcl.trans hGf
    convert h using 1
    ext g
    constructor
    · intro hg; exact ⟨⟨g, hKf hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact Subgroup.mem_subgroupOf.1 hx
  refine (GlobalTheory.AdelicU.isCompact_levelFin D.sp.cm.sig V.gram Λ).of_isClosed_subset hKcl ?_
  intro k hk
  refine GlobalTheory.AdelicU.mem_levelFin.2 ⟨?_, hKi k hk⟩
  have := hKf hk
  rw [GlobalTheory.AdelicU.GfC_eq] at this
  exact this

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RkNs

theorem small_entries_and_strings_avoid_excluded : ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r t : ℕ), r + 2 ≤ t → ∀ k ∈ ({(t : ℤ) - 1, 1 - (t : ℤ), (t : ℤ) + 1, -((t : ℤ) + 1)} : Set ℤ), (∀ β : ℂ, β ≠ 0 → ‖β‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → ‖β⁻¹‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → β ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2)) ∧ ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → x ≠ 1 → ∀ β ∈ GlobalTheory.LFun.seg w x t, (β : ℂ) ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2) := by
  intro K _ _ w r t hrt k hk
  have hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast GlobalTheory.LFun.one_lt_absNorm w
  have hN0 : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by linarith
  have hkabs : (r : ℤ) < k ∨ k < -(r : ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h | h <;> subst h <;> omega
  refine ⟨?_, ?_⟩
  · intro β hβ0 h1 h2 heq
    have hn : ‖β‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
      rw [heq, GlobalTheory.LFun.norm_npow]
      congr 1
      simp
    rcases hkabs with hk' | hk'
    · have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (r : ℝ) < (k : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
    · have hinv : ‖β⁻¹‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        rw [norm_inv, hn, Real.rpow_neg hN0.le]
      have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (k : ℝ) < -(r : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
  · intro x hx1 hxne β hβ heq
    simp only [GlobalTheory.LFun.seg, Multiset.mem_map, Finset.mem_range] at hβ
    obtain ⟨i, -, rfl⟩ := hβ
    set c : ℂ := (k : ℂ) / 2 - (((t : ℂ) - 1) / 2 - (i : ℂ)) with hc
    have hsplit : GlobalTheory.LFun.npow w ((k : ℂ) / 2) =
        GlobalTheory.LFun.npow w (((t : ℂ) - 1) / 2 - (i : ℂ)) * GlobalTheory.LFun.npow w c := by
      rw [← GlobalTheory.LFun.npow_add]
      congr 1
      rw [hc]; ring
    rw [Units.val_mul, GlobalTheory.LFun.coe_npowU, hsplit, mul_comm] at heq
    have hx : (x : ℂ) = GlobalTheory.LFun.npow w c :=
      mul_left_cancel₀ (GlobalTheory.LFun.npow_ne_zero w _) heq
    have him : c.im = 0 := by
      rw [hc]; simp
    have hre : c.re = 0 := by
      have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ c.re = 1 := by
        rw [← GlobalTheory.LFun.norm_npow, ← hx, hx1]
      rcases lt_trichotomy c.re 0 with h | h | h
      · have := Real.rpow_lt_one_of_one_lt_of_neg hN h
        linarith
      · exact h
      · have := Real.one_lt_rpow hN h
        linarith
    have hc0 : c = 0 := Complex.ext hre him
    apply hxne
    ext
    rw [hx, hc0, GlobalTheory.LFun.npow, Complex.cpow_zero, Units.val_one]

end GlobalTheory.RkNs
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RedOne

theorem redFn_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (PP : Pl D.host.E), Lev.finE V g ∈ Formalism.L2.DIV.St β → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V g) = 1 := by
  intro D V β g PP hS h1
  classical
  exact GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS
    (fun v hv => by rw [Finset.mem_singleton] at hv; subst hv; exact h1) (Finset.mem_singleton_self _)

end GlobalTheory.ChainOnto.RedOne
end
