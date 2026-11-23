module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle252
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015

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

namespace GlobalTheory.Core.Rk.IP

theorem frameLat_isSelfDualC {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [h]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

end GlobalTheory.Core.Rk.IP
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

namespace GlobalTheory.Core.Rk.RTr

theorem cuspFormsArchimedeanKFinite_rightTranslate_finite : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ k ∈ GfC A,
    ∀ u ∈ A0 θ A cA, rTr A k u ∈ A0 θ A cA :=
  fun _ _ _ _ hθ _ hk _ hu => rTr_fin_mem_cuspForms hθ Kinf_le hu hk

end GlobalTheory.Core.Rk.RTr
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
namespace GlobalTheory.Grow.IoHeight

theorem height_io_le (D : D7) (A : HSp D) (g₁ g₂ : GA D A) :
    GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F (finSumFinEquiv (m := A.rank) (n := A.rank))
    (Formalism.L2.Theta.matHom (dblSp A) (io A (g₁, g₂))) (Formalism.L2.Theta.matHom A g₁) (Formalism.L2.Theta.matHom A g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem main : ∀ (D : D7) (A : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D A, GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂) ^ c :=
  fun D A => ⟨1, 1, fun g₁ g₂ => by simpa using height_io_le D A g₁ g₂⟩

end GlobalTheory.Grow.IoHeight
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

noncomputable section

namespace GlobalTheory.Cont.HeightIo

theorem height_io_le_mul {D : D7} (V : HSp D) (g₁ g₂ : GA D V) :
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F finSumFinEquiv
    (Formalism.L2.Theta.matHom (dblSp V) (io V (g₁, g₂))) (Formalism.L2.Theta.matHom V g₁) (Formalism.L2.Theta.matHom V g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤
    ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem height_io_bound : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c := by
  intro D V
  refine ⟨1, 1, fun g₁ g₂ => ?_⟩
  rw [one_mul, pow_one]
  exact height_io_le_mul V g₁ g₂

end GlobalTheory.Cont.HeightIo

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.VacOffS

variable {D : D7}

theorem exists_under (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩




theorem latO_at_le {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {NS NT : ℕ}
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ LS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ LT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E)) (fun u => u = v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set M : ℕ := NS * NT with hMdef
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hv
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  have hval : HeightOneSpectrum.valuation D.host.F v (M : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ intAf D.host.F, α = algebraMap D.host.F _ (M : D.host.F) * γ := by
    refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
    · rw [map_mul, AlgHom.commutes]
      by_cases hw : w = v
      · subst hw
        refine mul_mem (hα w) ?_
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀, hval, inv_one]
      · rw [hP w hw, zero_mul]; exact zero_mem _
    · rw [mul_comm α, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]
  have hs' : s ∈ L0c D S := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hs
  have ht' : t ∈ L0c D T := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact ht
  refine AddSubgroup.subset_closure ⟨γ, hγ, fun w hw => (hw trivial).elim, a, ha, _, hS s hs', _, hT t ht', ?_⟩
  ext i j
  simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.VacLat.pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]
  congr 1
  rw [Algebra.smul_def, map_natCast, hMdef]
  simp only [star_mul', star_natCast, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.ChainOnto.VacOffS


open GlobalTheory.ChainOnto.VacOffS in
theorem GlobalTheory.ChainOnto.fock_vacFin_off :
    ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, ∀ v ∉ c.S, VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D _ c hc k _ s s' hs hs' p hp φ v hv
  classical
  obtain ⟨ξ, f₀, hf₀, e, he, hth⟩ := hp.vec
  obtain ⟨NS, hNS, hNSv⟩ := hs.base
  obtain ⟨NT, hNT, hNTv⟩ := hs'.base
  obtain ⟨hr, ξ', hL⟩ := hs.lev
  have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    obtain ⟨P, hP⟩ := exists_under (D := D) v
    have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
    have h1 := hNSv P hPv
    have h2 := hNTv P hPv
    intro h
    rw [← hP] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact h1 h
    · exact h2 h
  have hle := latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
  have hoff : ∀ PP ∈ s.L.Pg ∪ ∅, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro PP hPP h0
    rw [Finset.union_empty, hL] at hPP
    exact hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hfix : ∀ u ∈ latO s.V s'.V (frameLat s.V : Set (Fin s.V.rank → D.host.E))
      (frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
      heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
      (GlobalTheory.VacGood.infPart_latO (hle hu))
      (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
        (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
  refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
  · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_comp_one {D : D7} {S T : HSp D} (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (1, h) (om (g, 1) f) = om (g, h) f := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  ext <;> simp

theorem rTrans_liftS {D : D7} {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T))
    (G : GA D T → ℂ) (f : WO S T → ℂ) (g : GA D S) :
    rTrans g (liftS om ν 𝓕 G f) = liftS om ν 𝓕 G (om (g, 1) f) := by
  funext x
  simp only [rTrans, liftS_apply]
  congr 1
  funext h
  have e : ((x, h) : GA D S × GA D T) * (g, 1) = (x * g, h) := by simp
  rw [← e, map_mul, Module.End.mul_apply]

theorem doubleStep_of_laws : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  intro D hBF hFB hLink hHand hFlat ψ σ B J B' s₁ s₂ l vL Φ₁ Φ₂ φ G g hΦ₁ hΦ₂ hφ hG hG'
  have hfl := GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hFlat ψ
  have hΞ₁ : ∀ h₁, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) := fun h₁ =>
    hfl.1 _ B J s₁ _ (s₁.weil.om_pres _ _ hΦ₁)
  have hΞ₂ : ∀ h₁ h₂, IsThetaFunO ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := fun h₁ h₂ =>
    hfl.2 _ J B' s₂ _ (s₂.weil.om_pres _ _ hΦ₂)
  have hL := fun h₁ => hLink ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ _ hφ (hΞ₁ h₁)
  refine ⟨fun h₁ h₂ => hHand ψ σ J B' s₂ vL _ _ (hL h₁).1 (hΞ₂ h₁ h₂), ?_⟩
  refine ⟨fun h₁ => J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)), ?_, ?_⟩
  · have := hBF ψ (σ + 1) B J s₁ φ (s₂.lift G Φ₂) (s₁.om (g, 1) Φ₁) hφ hG' (s₁.weil.om_pres _ _ hΦ₁)
    simp only [om_comp_one] at this
    convert this using 2
    exact rTrans_liftS _ _ _ _ _ _
  · intro h₁
    have := hFB ψ σ J B' s₂ vL _ G (s₂.om (h₁, 1) Φ₂) (hL h₁).1 hG (s₂.weil.om_pres _ _ hΦ₂)
    simp only [om_comp_one] at this
    convert this using 1
    · rfl
    · show J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)) = _
      rw [(hL h₁).2]
      congr 1
      exact rTrans_liftS _ _ _ _ _ _

end GlobalTheory.Unf

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspStab

theorem rder_stab : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ (A : ℕ) (φ : GA D V → ℂ), IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) → SmoothW θ V φ → (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) → IsCuspFun V φ → IsAutFun V (Rder θ V τ X φ) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g) ∧ SmoothW θ V (Rder θ V τ X φ) ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) (Rder θ V τ X φ))) ∧ IsCuspFun V (Rder θ V τ X φ) := by
  intro D θ hθ V U τ X hX A φ ha hU hs hg hc
  have hs' : φ ∈ SmFun θ V := hs
  have inv : ∀ k, k ∈ GfC V → (∀ g, φ (g * k) = φ g) → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g := by
    intro k hk e g
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hk τ X φ) g
    rw [show rTr V k φ = φ from funext e] at this
    exact this.symm
  have hcont : Continuous (Rder θ V τ X φ) := by
    refine GlobalTheory.Size.continuous_Rder_of_growth hθ hs' ha.cont hX (A := A) ?_
    simpa using hg [(τ, X), (τ, X)] (by simp [hX])
  have ha' : IsAutFun V (Rder θ V τ X φ) :=
    { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (ha.left γ hγ) τ X
      level := by
        obtain ⟨U₀, hU₀, e⟩ := ha.level
        exact ⟨U₀, hU₀, fun k hk hf => inv k hf (e k hk hf)⟩
      cont := hcont }
  refine ⟨ha', fun k hk hf => inv k hf (hU k hk hf), Rder_mem hs' hX, fun l hl => ?_, ?_⟩
  · have := hg (l ++ [(τ, X)]) (by
      intro p hp
      rcases List.mem_append.1 hp with h | h
      · exact hl p h
      · rw [List.mem_singleton.1 h]; exact hX)
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this
  · refine (isCuspFun_iff ha'.left).2 fun W hW => funext fun x => ?_
    have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff ha.left).1 hc W hW
    have := GlobalTheory.CuspLie.hasDerivAt_constTermOn (cocompact_single hW) ha.left ha.cont ha'.left ha'.cont
      (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
      (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hs' hX)) x
    rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
    exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

end GlobalTheory.CuspStab

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZeroAt

variable {D : D7}

theorem mulVec_idAt {m n : ℕ} (M : Mx D m n) {P : Pl D → Prop} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) :
    ∀ i, (M *ᵥ y) i ∈ idAt D P := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittProjectionZero_mem_latticeCompletion_of_splits {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : d.p0 *ᵥ y ∈ latV S₀ L₀ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P S₀ L₀ _ hL₀).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hm v hv _).1 (GlobalTheory.FinPlLoc.smul_latV v he hy)).2.2

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {P : Pl D → Prop}
    (hL : Submodule.IsLattice D.host.E L) (hm : ∀ v, P v → MonoAt d L L₀ v) {u : Fin T₀.rank → AE D}
    (hu : u ∈ latV T₀ L₀ P) : d.j0 *ᵥ u ∈ latV T L P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T L _ hL).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hu), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact GlobalTheory.FinPl.VacFlat.wittCoreInclusion_mem_latticeCompletionAtPlace d (hm v hv) (GlobalTheory.FinPlLoc.smul_latV v he hu)

end GlobalTheory.FinPl.ExtZeroAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem GlobalTheory.GlobFin.cong_entry {D : D7} {S : HSp D} {I : Ideal (AE D)} {h : GA D S} (hh : h ∈ congGrp S I) (i j : Fin S.rank) :
    mt S h i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ I := by
  have h1 := congrArg (fun A : GL (Fin S.rank) (AE D ⧸ I) => A.1 i j) (MonoidHom.mem_ker.mp hh)
  rw [← Ideal.Quotient.eq]
  have h2 : Ideal.Quotient.mk I ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ I)) i j := by
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, *]
  rw [h2]
  simpa [Formalism.L2.Theta.mt, Matrix.GeneralLinearGroup.map] using h1

theorem GlobalTheory.GlobFin.mem_GfC {D : D7} {S : HSp D} {x : GA D S} (hx : x ∈ congGrp S (idAt D (fun _ => True))) : x ∈ GfC S := by
  show infHom S x = 1
  ext i j
  have h := GlobalTheory.GlobFin.cong_entry hx i j
  have hk : mt S x i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ RingHom.ker (infPart D) :=
    (inf_le_left : idAt D (fun _ => True) ≤ _) h
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hk
  have : ((infHom S x : GL _ _) : Matrix _ _ _) i j = infPart D (mt S x i j) := rfl
  rw [this, hk]
  simp [Matrix.one_apply, apply_ite]

theorem GlobalTheory.GlobFin.fin_rep : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := by
  intro D S g
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, hS⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)
  obtain ⟨x, hx, u, hu, rfl⟩ := (hS S).1 g
  refine ⟨x, GlobalTheory.GlobFin.mem_GfC hx, fun P y hy => ?_⟩
  have hy0 : ∀ j, y j ∈ idAt D (fun _ => True) := by
    intro j
    refine Ideal.mem_inf.mpr ⟨(Ideal.mem_inf.mp (hy j)).1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  have hu1 : Formalism.L2.Theta.mt S u *ᵥ y = y := by
    funext i
    have hz : ∀ j, (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j = 0 := by
      intro j
      have ha := (hOff _).mp (GlobalTheory.GlobFin.cong_entry hu i j)
      have hb := (hAt _).mp (hy0 j)
      calc (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j
          = (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * (ε * y j) := by rw [hb]
        _ = (ε * (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) * y j := by ring
        _ = 0 := by rw [ha, zero_mul]
    have hsum : ((Formalism.L2.Theta.mt S u - 1) *ᵥ y) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      exact Finset.sum_eq_zero fun j _ => hz j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at hsum
    exact hsum
  rw [mt_mul, ← Matrix.mulVec_mulVec, hu1]
end
