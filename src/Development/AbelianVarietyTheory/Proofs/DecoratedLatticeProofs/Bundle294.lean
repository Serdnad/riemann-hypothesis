module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.iwasawa_isotropicStabilizer_inertPlace : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  first | exact @GlobalTheory.InertIwasawaIso.iwasawa_inert | exact GlobalTheory.InertIwasawaIso.iwasawa_inert | (intros; apply GlobalTheory.InertIwasawaIso.iwasawa_inert <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_lowerLeft_zero {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) (i j : Fin n) :
    mat g (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  have hx : (Pi.single (Fin.castAdd n j) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
    rw [upperHalf, LinearMap.mem_ker]
    funext k
    rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega) _
  have h1 := (hg (Pi.single (Fin.castAdd n j) 1)).1 hx
  rw [upperHalf, LinearMap.mem_ker] at h1
  have h2 := congrFun h1 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right, mulVec_single_one] at h2
  exact h2

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_levi_mul {D : D7} {A : HSp D} {μ : D.host.E} {κ : GA D (dblSp A) ≃* G D A.rank}
    (hκ : IsChart A μ κ) (p : GA D (dblSp A)) (hp : κ p ∈ P D A.rank) :
    leviMat finSumFinEquiv (mt (dblSp A) p) * rat A.gram⁻¹ = rat A.gram⁻¹ * blkA (mat (κ p)) := by
  ext i j
  have h := congrFun (congrFun (hκ p) (Fin.castAdd A.rank i)) (Fin.castAdd A.rank j)
  simp only [Matrix.mul_apply, Fin.sum_univ_add] at h
  simp only [Matrix.mul_apply, leviMat, blkA, toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, submatrix_apply, add_mul,
    Finset.sum_add_distrib, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp only [Tm, rat, Matrix.map_apply, submatrix_apply, id, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr, dblDec, stackRows,
    fromRows_apply_inl, fromRows_apply_inr, chart_lowerLeft_zero hp, mul_zero, Finset.sum_const_zero, add_zero] at h
  simp only [Matrix.add_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib, rat, Matrix.map_apply]
  exact h.symm

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_aP_eq_det : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (p : siegel A) (a : GL (Fin A.rank) (AE D)), blkA (mat (κ p)) = a.1 →
      aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A μ hμ κ hκ p a ha
  have hP : κ p ∈ P D A.rank := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ p).1 p.2
  have h1 := congrArg Matrix.det (chart_levi_mul hκ p hP)
  rw [ha, Matrix.det_mul, Matrix.det_mul] at h1
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (gram_det_ne A)
  refine Units.ext ?_
  change (leviMat finSumFinEquiv (mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  exact hu.mul_left_cancel (by rw [mul_comm]; exact h1)

end GlobalTheory.StdUnn

end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isCartanInv_standardInvolution_doubledGram : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ s : RealMat (dblSp A), IsStdInv A μ s → ∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (s τ) := by
  first | exact @GlobalTheory.CartStd.isCartanInv_stdInv | exact GlobalTheory.CartStd.isCartanInv_stdInv | (intros; apply GlobalTheory.CartStd.isCartanInv_stdInv <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartRat

variable {D : D7}

theorem mem_GF_iff {n : ℕ} (g : G D n) : g ∈ GF D n ↔ mat g ∈ ratMx D (n + n) (n + n) := by
  constructor
  · rintro ⟨γ, -, h⟩
    exact ⟨γ.1, congrArg Units.val h⟩
  · rintro ⟨γ, hγ⟩
    replace hγ : rat γ = mat g := hγ
    have h : γᴴ * Jst D n * γ = Jst D n := by
      apply rat_injective
      rw [rat_mul, rat_mul, rat_conjTranspose, hγ]
      exact g.2
    have hdet : γ.det ≠ 0 := by
      intro h0
      have hu : IsUnit (mat g).det := Matrix.isUnits_det_units _
      rw [← hγ, rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
      have h01 : (0 : AE D) = 1 := isUnit_zero_iff.1 hu
      exact zero_ne_one (incA_injective (D := D) (by rw [map_zero, map_one]; exact h01))
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hdet, h, Units.ext hγ⟩

end GlobalTheory.StdUnn.ChartRat

namespace GlobalTheory.StdUnn

theorem chart_mem_GF_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  intro D A μ hμ κ hκ g
  obtain ⟨-, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTi : rat (Tm A μ)⁻¹ * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hdet, rat_one]
  have hTi' : rat (Tm A μ) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hdet, rat_one]
  have e1 : mat (κ g) = rat (Tm A μ)⁻¹ * (mt (dblSp A) g * rat (Tm A μ)) := by
    rw [← hκ g, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have e2 : mt (dblSp A) g = rat (Tm A μ) * mat (κ g) * rat (Tm A μ)⁻¹ := by
    rw [hκ g, Matrix.mul_assoc, hTi', Matrix.mul_one]
  rw [GlobalTheory.MixModel.mem_GQ_iff, ChartRat.mem_GF_iff]
  constructor
  · intro h
    rw [e1]
    exact ratMx_mul (rat_mem _) (ratMx_mul h (rat_mem _))
  · intro h
    rw [e2]
    exact ratMx_mul (ratMx_mul (rat_mem _) h) (rat_mem _)

end GlobalTheory.StdUnn
end

section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.continuous_standardUnitaryChart_and_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  first | exact @GlobalTheory.StdUnn.chart_continuous | exact GlobalTheory.StdUnn.chart_continuous | (intros; apply GlobalTheory.StdUnn.chart_continuous <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_maximalCompactUnn_component_standardCartanInv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n : ℕ) (μ : D.host.E), IsSkew μ → ∃ k ∈ K D n, ∀ τ, compAt θ τ (mat k) = stdInv n μ τ := by
  first | exact @GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv | exact GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv | (intros; apply GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parOfVal_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ParOfVal D := by
  intro hP D hM hL c hc j hj s hs x w B hv hf
  obtain ⟨e, he⟩ := GlobalTheory.T.stageCuspFormValue_mem_fullSphericalHecke_eigenpart hP D hM hL c hc j hj s hs x w B hv hf
  exact (GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters hP D c hc j hj s hs x e he).2 w B hv hf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem eigSpan_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → LevFacts D → EigSpan D := by
  intro hC D hF _ hL c hc j hj s hs
  have hspan := GlobalTheory.T.multiplicitySpace_span_fullSphericalHecke_eigenparts hC D hF hL c hc j hj s hs
  have hpar := GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters hC D c hc j hj s hs
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 ?_
  rintro u ⟨e, he⟩
  by_cases h0 : u = 0
  · rw [h0]; exact Submodule.zero_mem _
  · exact Submodule.subset_span ((hpar u e he).1 h0)

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

theorem _root_.GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiTheta ψ B.A S B'.A (contr l S vL f₁ f₂) ∧ (∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ), contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) = biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂)) ∧ ∀ (P : Pl D → Prop) (LA : Lat B.A) (LS : Lat S) (LA' : Lat B'.A) (M : Lat B.V₀) (M' : Lat B'.V₀), IsSelfDualC B.A LA → IsSelfDualC S LS → IsSelfDualC B'.A LA' → IsSelfDualC B.V₀ M → IsSelfDualC B'.V₀ M' → (∀ v, P v → (∃ LL, OrthAt B.o M LA LL v) ∧ ∃ LL, OrthAt B'.o M' LA' LL v) → Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → BiVacAt ψ LA LS LA' P (contr l S vL f₁ f₂) := by
  first | exact @GlobalTheory.ContrComb.contr_comb_main | exact GlobalTheory.ContrComb.contr_comb_main | (intros; apply GlobalTheory.ContrComb.contr_comb_main <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

namespace GlobalTheory.Core.Rk.SchPeriod

theorem theta_eq_sum_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x : Mx D B.rank A.rank, (Summable fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => ‖sch ψ A B ν 𝓨 f (x + rat ξ)‖) ∧ HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ)) (f ((dblDec A).extX B x)) := by
  intro D ψ hψ A B ν 𝓨 hcov f hf x
  have hF : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B ((dblDec A).extX B x) f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ (dblSp A) B).1 _ _ hf
  have h1 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ f hf).1
  have h5 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ _ hF).2.2.2.2 0
  have h0 : heisO ψ (dblSp A) B ((dblDec A).extX B x) f ((dblDec A).ext0 B 0) = f ((dblDec A).extX B x) := by
    rw [map_zero]
    simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have H : HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ))
      (f ((dblDec A).extX B x)) := by
    rw [h0] at h5
    convert h5 using 1
    funext ξ
    rw [h1, add_comm]
    rfl
  exact ⟨summable_norm_iff.2 H.summable, H⟩

end GlobalTheory.Core.Rk.SchPeriod

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

namespace GlobalTheory.ChainTw

theorem isPar_flat_of_le {D : D7} {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} (hr : D.R.r ≤ s.V.rank)
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB : IsPar u B) :
    IsPar (⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) B := by
  refine ⟨fun h => ?_, fun v hv => ?_⟩
  · have h2 : ((⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) : SmT (flat c w j s hr).M →ₗ[ℂ] (GA D (flat c w j s hr).V → ℂ)) = 0 :=
      (Submodule.coe_eq_zero).2 h
    exact hB.1 ((Submodule.coe_eq_zero).1 h2)
  · have h3 := hB.2 v hv
    unfold ParFun at h3 ⊢
    exact h3

theorem bounded_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2) := by
  have hrank : s'.V.rank = D.R.r := by
    rw [hflat.rank]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hbd0 := GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay hCRD D (GlobalTheory.T.thetaChain_level_properties D) c hc 0 hj s' hflat u' B hB'
  rw [hrank] at hbd0
  exact hbd0

theorem conjStable_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧
      (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w) := by
  have hex : ∃ v, PiLocalization₂.val u' v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hB'.1
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s'.V → ℂ := fun g => conj (PiLocalization₂.val u' v g) with hfdef
  have hPF : ParFun c s' (PiLocalization₂.val u' v) B := hB'.2 v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s'.V c.S f B := ((GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc 0 hj s' hflat).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc 0 hj s' hflat
  obtain ⟨hcont, ⟨C, hC⟩, hinv, _⟩ := h4a u' v
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s'.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  exact GlobalTheory.T.boundedAutomorphic_parameters_star_stable D s'.V c.S f hfmem B h3

end GlobalTheory.ChainTw

namespace GlobalTheory.ChainTw

theorem lPos_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LPos D := by
  intro hCRD D c w hw j hj s hs hj0 u B hB
  subst hj0
  have hc := hw.com
  obtain ⟨hr, hL, hflat⟩ := hs
  have hle := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw 0 hj s ⟨hr, hL, hflat⟩ hr
  have hB' := isPar_flat_of_le hr hle u B hB
  have hbd : GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) :=
    GlobalTheory.LiftPole.Bounded.mono (bounded_first_member hCRD hc hj hflat _ B hB') (by linarith)
  refine ⟨hbd, fun k hk => ?_⟩
  have hst := conjStable_first_member hCRD hc hj hflat _ B hB'
  have hch := hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hrt : ((D.R.r : ℝ) / 2) + 1 < (1 + (D.R.t : ℝ)) / 2 := by
    have h5 : D.R.r + 5 ≤ D.R.t := by simpa [Formalism.BasicNotions.Ranks.r] using D.R.rank_add_five_le
    have h5' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast h5
    linarith
  obtain ⟨l, hl, he⟩ := GlobalTheory.T.euler_product_conjugation_stable_parameters_pos D c.S B (c.μ (k + 1)) D.R.r ((D.R.r : ℝ) / 2) ((1 + (D.R.t : ℝ)) / 2) hch.1 hch.2
    (hc.unr ⟨k, hk⟩) hbd hrt hst
  refine ⟨l, hl, ?_⟩
  rw [← he]
  congr 1
  push_cast
  ring

end GlobalTheory.ChainTw
end
