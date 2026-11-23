module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle532
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle366
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle515
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle507
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle209
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuity
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle747
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle633
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle625
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle627
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergence
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift

@[expose] public section

section

open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.SiegelWeil

theorem swSection_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  intro D ψ A B χ ω hω f hf ν 𝓖 hν
  rw [GlobalTheory.Core.Rk.IP.swSection_eq_swSec A B ν 𝓖 ω f]
  exact (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ ω hω ν 𝓖 hν f hf).2

end GlobalTheory.CompanionTheory.SiegelWeil
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.QKAvg.RadMeas

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem absDet_eq (d : HypDec B W t) (m : GlobalTheory.RegSW.stab d) (g : GA D W) (a : GL (Fin t) (AE D))
    (hm : (m : GA D B) = d.emb0 g * d.levi a) :
    GlobalTheory.RegSW.absDet d m = absA D (Matrix.GeneralLinearGroup.det a) := by
  have h : mt B (m : GA D B) ⬝ d.jX = d.jX ⬝ a.1 := by
    rw [hm, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  have e : GlobalTheory.RegSW.onX d m = a :=
    Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d m)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, e]

theorem regular_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : μ.Regular := inferInstance

theorem sFinite_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : SFinite μ := inferInstance



theorem map_lr {n : ℕ} (a : GL (Fin t) (AE D)) (h : GL (Fin n) (AE D))
    (hh : absA D (Matrix.GeneralLinearGroup.det h) = 1) (β : Measure (Mx D t n)) (hβ : β.IsAddHaarMeasure) :
    β.map (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) =
      ((absA D (Matrix.GeneralLinearGroup.det a) ^ n)⁻¹ : ℝ≥0) • β := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t n
  haveI : IsTopologicalAddGroup (Mx D t n) := i1
  haveI : LocallyCompactSpace (Mx D t n) := i2
  haveI : SecondCountableTopology (Mx D t n) := i3
  haveI : T2Space (Mx D t n) := i4
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE a h
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ n *
      absA D (Matrix.GeneralLinearGroup.det h) ^ t :=
    GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n a h
  rw [hh, one_pow, mul_one] at hc
  have e : (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) = φ :=
    funext fun y => (GlobalTheory.ModuLR.lrCE_apply a h y).symm
  have hA : absA D (Matrix.GeneralLinearGroup.det a) ^ n ≠ 0 := pow_ne_zero _ ((Group.isUnit _).map (absA D)).ne_zero
  haveI := regular_of_haar β
  have key := addEquivAddHaarChar_smul_map β φ
  rw [e, ← hc]
  rw [← hc] at hA
  conv_rhs => rw [← key]
  rw [smul_smul, inv_mul_cancel₀ hA, one_smul]



theorem exists_radN_measure (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] :
    ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d,
      νN.map (fun n : radN d => MulAut.conjNormal m n) =
        ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t W.rank
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t W.rank) := i1
  haveI : LocallyCompactSpace (Mx D t W.rank) := i2
  haveI : SecondCountableTopology (Mx D t W.rank) := i3
  haveI : T2Space (Mx D t W.rank) := i4
  haveI : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D t t) := j1
  haveI : LocallyCompactSpace (Mx D t t) := j2
  haveI : SecondCountableTopology (Mx D t t) := j3
  haveI : T2Space (Mx D t t) := j4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hcl : IsClosed (skewA D t : Set (Mx D t t)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D t) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : BorelSpace (skewA D t) := Subtype.borelSpace _
  haveI : T2Space (skewA D t) := inferInstance
  haveI : SecondCountableTopology (skewA D t) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let κ : Measure (skewA D t) := Measure.addHaar
  let β : Measure (Mx D t W.rank) := Measure.addHaar
  haveI hκ : κ.IsAddHaarMeasure := inferInstance
  haveI hβ : β.IsAddHaarMeasure := inferInstance
  haveI := sFinite_of_haar κ
  haveI := sFinite_of_haar β
  obtain ⟨Ψ, hΨ, hH, hR⟩ := GlobalTheory.T.unipotent_radical_haar_from_product D B W t d κ β hκ hβ
  refine ⟨(κ.prod β).map Ψ, hH, hR, ?_⟩
  rintro m ⟨g, a, hm⟩
  let f₁ : skewA D t → skewA D t := skewConj a.1
  let f₂ : Mx D t W.rank → Mx D t W.rank := fun b => (a.1 ⬝ b ⬝ (matHom W g⁻¹).1 : Mx D t W.rank)
  have hf₁ : Continuous f₁ := Continuous.subtype_mk
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hf₂ : Continuous f₂ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hL : ∀ n : radN d, (((MulAut.conjNormal m n : radN d) : GlobalTheory.RegSW.stab d) : GA D B) =
      (m : GA D B) * ((n : GlobalTheory.RegSW.stab d) : GA D B) * (m : GA D B)⁻¹ := fun n => by
    rw [MulAut.conjNormal_apply]
    rfl
  have hconj : ∀ p, MulAut.conjNormal m (Ψ p) = Ψ (Prod.map f₁ f₂ p) := by
    rintro ⟨c, b⟩
    apply Subtype.ext
    apply Subtype.ext
    refine (hL _).trans ?_
    rw [hΨ (c, b), hΨ (Prod.map f₁ f₂ (c, b)), hm]
    exact conj_coord d g a c b
  have hcm : Measurable fun n : radN d => MulAut.conjNormal m n := by
    have : (fun n : radN d => MulAut.conjNormal m n) = Ψ ∘ Prod.map f₁ f₂ ∘ Ψ.symm := by
      funext n
      simp only [Function.comp]
      rw [← hconj, Ψ.apply_symm_apply]
    rw [this]
    exact (Ψ.continuous.comp ((hf₁.prodMap hf₂).comp Ψ.symm.continuous)).measurable
  have hk := GlobalTheory.T.haar_skew_matrices_conj_scaling D t κ hκ a
  have hb := map_lr a (matHom W g⁻¹) (GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw.absA_det_matHom g⁻¹) β hβ
  rw [Measure.map_map hcm Ψ.continuous.measurable]
  have hc : (fun n : radN d => MulAut.conjNormal m n) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext p
    exact hconj p
  rw [hc, ← Measure.map_map Ψ.continuous.measurable (hf₁.prodMap hf₂).measurable,
    ← Measure.map_prod_map κ β hf₁.measurable hf₂.measurable]
  change (((κ.map (skewConj a.1)).prod (β.map _)).map Ψ) = _
  rw [hk, hb, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul,
    absDet_eq d m g a hm, pow_add, mul_inv, mul_comm]
  all_goals exact Ψ.continuous.measurable.aemeasurable

end GlobalTheory.CompanionTheory.QKAvg.RadMeas
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem weil_fock_mem (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) (hr : ResEta D χ V.rank) (θ : InfFam D) (hθ : IsInfFam θ)
    (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (hω : IsWeilSch ψ χ θ V μ ω)
    (l : D.what₂.Tau → ℝ) (hl : HasRealPar ψ θ l) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (Φ : schwartzA θ V.rank n) (hΦ : Φ.1 ∈ fockA θ V n l s)
    (k : G D n) (hk : k ∈ K D n) : (ω k Φ).1 ∈ fockA θ V n l s := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  obtain ⟨hth, N, hN⟩ := hfock
  have hk' : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    ⟨hdat.om_pres _ f hth, N,
      GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ (κ.symm k) (hcomm _ hk') N f hth hN⟩
  have hmem := GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have htrk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htrk
  exact Eq.mpr (congrArg (fun φ : Mx D V.rank n → ℂ => φ ∈ fockA θ V n l s) htrk) hmem

theorem weilKFin : WeilKFin := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  have hfin := GlobalTheory.StdUnn.KFin.fock_kfinite D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  set S := Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ} with hS
  refine ⟨S.map (schwartzA θ V.rank n).subtype, Module.Finite.map S _, ?_, ?_⟩
  · rw [hS, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Ψ, ⟨k, hk, rfl⟩, rfl⟩
    exact weil_fock_mem D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ k hk
  · intro k hk
    exact ⟨ω k Φ, Submodule.subset_span ⟨k, hk, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.weil_representation_continuity : WeilCont := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilCont | exact GlobalTheory.CompanionTheory.ThTot.weilCont | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilCont <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS.FockSplit

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

section Box

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem isPureFin_box (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v))
    (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b ((GlobalTheory.CompanionTheory.WhitFree.boxF A).indicator (fun _ => (1 : ℂ)))
      (fun v => (A v).indicator 1) := by
  classical
  refine ⟨fun v => ?_, ?_, fun X => ?_⟩
  · haveI : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
      (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).isEmbedding.t2Space
    have hcl : IsClopen (A v) := ⟨(hA v).1.isClosed, (hA v).2⟩
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
      HasCompactSupport.intro (hA v).1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ A v
    · exact ⟨A v, (hA v).2, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        rfl⟩
    · exact ⟨(A v)ᶜ, hcl.compl.isOpen, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    refine hv ?_
    show (A v).indicator 1 = _
    rw [hS v h]
  · by_cases hX : X ∈ GlobalTheory.CompanionTheory.WhitFree.boxF A
    · rw [Set.indicator_of_mem hX]
      exact (finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (hX v) _).symm
    · rw [Set.indicator_of_notMem hX]
      obtain ⟨v₀, hv₀⟩ : ∃ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v X ∉ A v := by
        by_contra h
        push_neg at h
        exact hX h
      refine (finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_).symm
      have hfin := Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b X)
      refine (hfin.union S.finite_toSet).subset fun v hv => ?_
      by_contra h
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not, Finset.mem_coe] at h
      apply hv
      show (A v).indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projV v X) = 1
      rw [hS v h.2]
      exact Set.indicator_of_mem h.1 _

end Box

theorem exists_fin_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {P : M → Prop}
    (hs : ∀ (a : ℂ) (x : M), P x → P (a • x)) {x : M} (hx : x ∈ Submodule.span ℂ {y | P y}) :
    ∃ (N : ℕ) (f : Fin N → M), x = ∑ j, f j ∧ ∀ j, P (f j) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, fun _ => x, by simp, fun _ => h⟩
  | zero => exact ⟨0, Fin.elim0, by simp, fun j => j.elim0⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    obtain ⟨N', f', rfl, hf'⟩ := hy
    refine ⟨N + N', Fin.append f f', by simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right], fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [Fin.append_left] using hf i
    · simpa [Fin.append_right] using hf' i
  | smul a x _ hx =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    exact ⟨N, fun j => a • f j, by rw [Finset.smul_sum], fun j => hs a _ (hf j)⟩

variable {D : D7} {n : ℕ}

theorem evalPoly_monomial_mul {m : ℕ} (e : D.what₂.Tau × Fin m × Fin n × Bool →₀ ℕ) (a c : ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.monomial e (a * c)) z = a * evalPoly (MvPolynomial.monomial e c) z := by
  simp only [evalPoly, MvPolynomial.eval_monomial, mul_assoc]

theorem isMonoFock_smul {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : Mx D V.rank n → ℂ} (a : ℂ)
    (h : IsMonoFock θ V l s φ) : IsMonoFock θ V l s (a • φ) := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  refine ⟨e, a * c, g, d, bs, gv, hp, funext fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, evalPoly_monomial_mul, mul_assoc]

theorem gen_mem_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  classical
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b := Module.finBasis D.host.F D.host.E
  let tr : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun X i j => X j i
      invFun := fun Z j i => Z i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  let g' : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => g (tr X)
  have hg' : IsSB g' := ⟨hg.1.comp_continuous tr.continuous, hg.2.comp_homeomorph tr⟩
  obtain ⟨t, A, S, hA, hS, hdec⟩ := Box.exists_box_combN b g' hg'
  let ind : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
    fun a Z => (GlobalTheory.CompanionTheory.WhitFree.boxF (A a)).indicator (fun _ => (1 : ℂ)) (fun j i => Z i j)
  have hpure : ∀ a ∈ t, HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b (fun X => ind a fun i j => X j i)
      (fun v => (A a v).indicator 1) := fun a ha => isPureFin_box b (A a) S (hA a) (hS a ha)
  have hφ : (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) =
      ∑ e ∈ p.support, ∑ a ∈ t, g' a • (fun x : Mx D V.rank n =>
        evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) *
          gauss V l s (fun τ => compAt θ τ x) * ind a (fun i j => finPart D (x i j))) := by
    funext x
    have hp : evalPoly p (fun τ => compAt θ τ x) =
        ∑ e ∈ p.support, evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
      calc evalPoly p (fun τ => compAt θ τ x)
          = evalPoly (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
            rw [← p.as_sum]
        _ = _ := by simp only [evalPoly, map_sum]
    have hgx : g (fun i j => finPart D (x i j)) =
        ∑ a ∈ t, g' a * ind a (fun i j => finPart D (x i j)) :=
      hdec (fun j i => finPart D (x i j))
    rw [hp, hgx, Finset.sum_mul, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hφ]
  refine Submodule.sum_mem _ fun e _ => Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨e, p.coeff e, ind a, _, b, _, hpure a ha, rfl⟩

theorem fockA_le_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    fockA θ V n l s ≤ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  exact gen_mem_span θ V l s p g hg

end GlobalTheory.CompanionTheory.PfSWUS.FockSplit

namespace GlobalTheory.CompanionTheory.PfSWUS

theorem fockSplitK : PositivityTheory.PfSWUS.FockSplitK := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd _ k hk
  exact FockSplit.exists_fin_sum (fun a _ h => FockSplit.isMonoFock_smul a h)
    (FockSplit.fockA_le_span θ V l s (fockKStable D n V ψ χ θ μ ω H l s ν Φ hStd k hk))

end GlobalTheory.CompanionTheory.PfSWUS

end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_automorphic_of_convergence : GlobalTheory.Published.WeilThetaConvergence → PositivityTheory.PfSWUS.ThetaAuto := by
  first | exact @GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto | exact GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto | (intros; apply GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto <;> assumption)
end
end
