module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle748
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle564
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOne
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle749
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle719
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle715
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle710
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle584
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle303
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle362
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
import GroundTheory.LocalFields.PadicLogSeries
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger

@[expose] public section

section

open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)


theorem _root_.GlobalTheory.T.theta_section_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | exact GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | (intros; apply GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)], ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d, νN.map (fun n : radN d => MulAut.conjNormal m n) = ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | exact GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure <;> assumption)
end

section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.weil_representation_K_finite : WeilKFin := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilKFin | exact GlobalTheory.CompanionTheory.ThTot.weilKFin | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilKFin <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fock_splitting_maximal_compact : PositivityTheory.PfSWUS.FockSplitK := by
  first | exact @GlobalTheory.CompanionTheory.PfSWUS.fockSplitK | exact GlobalTheory.CompanionTheory.PfSWUS.fockSplitK | (intros; apply GlobalTheory.CompanionTheory.PfSWUS.fockSplitK <;> assumption)
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsChapter

theorem eisCells : PositivityTheory.GramSchwartzFunctions.EisCells :=
  GlobalTheory.T.eisenstein_cells_decomposition GlobalTheory.T.eisenstein_bruhat_decomposition GlobalTheory.T.eisenstein_rational_points GlobalTheory.T.eisenstein_siegel_parabolic_invariance
    (GlobalTheory.T.eisenstein_second_term_from_parts GlobalTheory.T.eisenstein_heisenberg_schwartz GlobalTheory.T.eisenstein_covariance GlobalTheory.T.eisenstein_vanishing GlobalTheory.T.eisenstein_unfolding_second_term GlobalTheory.T.eisenstein_theta_invariance)

end GlobalTheory.CompanionTheory.EisCellsChapter
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ExpProd

theorem val_unifU (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]
    exact GlobalTheory.CompanionTheory.UnifPow.valuation_unifU_lt_one k
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy1 : valuation k y < 1 := hy ▸ uniformizer_lt_one
    have hyO : y ∈ 𝒪[k] := hy1.le
    have hm : (⟨y, hyO⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact hy1.ne (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu)
    rw [(Zls.irreducible_unif (k := k)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    rw [← hy]
    exact (Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))).2 hm

theorem atUnif_unrChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (ξ : Fin n → ℂˣ) : PositivityTheory.SphericalProduct.atUnif k (fun i => unrChar k (ξ i)) = ξ :=
  funext fun i => unrChar_uniformizer k (ξ i) (val_unifU k)

theorem expToSat : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  intro E _ _ w c n N h σ P ξ hsub hmono ⟨y, hy0, hy⟩
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hd : ∑ _a : Fin n, 1 = n := by simp
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.CompanionTheory.StandardBlocks.stdBridge (w.adicCompletion E) n hd P.V P.ρ _ y hy0 hy
  have hadm : IsAdmissible P.ρ :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness (w.adicCompletion E)).1 _ P.V P.ρ P.smooth P.irred
  have hanti : PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif (w.adicCompletion E)
      (fun i => unrChar (w.adicCompletion E) (ξ i))) := by
    rw [atUnif_unrChar]
    exact fun i j hij => hmono i j hij
  have hsat := GlobalTheory.CompanionTheory.LocGL.expSat (w.adicCompletion E) n hd P.V P.ρ P.smooth hadm P.irred
    (fun i => unrChar (w.adicCompletion E) (ξ i)) (fun i => isUnram_unrChar _ _) hanti ⟨v, hv0, hv⟩
  rw [atUnif_unrChar] at hsat
  have hG := (GlobalTheory.CompanionTheory.SatakeBridge.satBridge E w n P.V P.ρ P.smooth P.irred ξ).1 hsat
  obtain ⟨x, hx⟩ := hG.exists_vec
  obtain ⟨S, f, hf⟩ := hsub
  have hsm : IsSmooth (locProd h w σ) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hSs : IsSmooth S.toRepresentation := GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S
  have hc := GlobalTheory.SatInd.isCompact_KGL (w := w) (n := n)
  obtain ⟨s, rfl⟩ := hf x
  obtain ⟨u, hu, hfu⟩ := GlobalTheory.LocGL.exists_mem_fixed_map_eq hSs hc f hx.2.1
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx.1 (by rw [← hfu, map_zero])
  have hfix : u.1 ∈ fixed (locProd h w σ) (GlobalTheory.LFun.KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu g hg)
  have hne : u.1 ≠ 0 := fun e => hu0 (Subtype.ext e)
  obtain ⟨B, hB, hBv⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (π := fun i => (σ i).ρ)
    (fun i => (σ i).smooth) (fun i => (σ i).irred) hfix hne
  have h1 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u (∑ a, B a) :=
    GlobalTheory.LFun.IsSatVecGL.of_map S.toSubmodule.subtype (fun g y => rfl) Subtype.val_injective hBv
  have h2 := h1.map (ρ' := P.ρ) f.toLinearMap (fun g y => f.isIntertwining _ _ g y) (by
    change f u ≠ 0
    rw [hfu]
    exact hx.1)
  change GlobalTheory.LFun.IsSatVecGL w P.ρ (f u) _ at h2
  rw [hfu] at h2
  exact ⟨fun i => (hB i).1, B, hB, h2.unique hx⟩

end GlobalTheory.CompanionTheory.ExpProd

end
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.length_formula_of_total_mass_one : PositivityTheory.SiegelWeilFormula.Densx.MassOne → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one | exact GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one | (intros; apply GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.cocompactness : CoCpt := by
  first | exact @GlobalTheory.CompanionTheory.MassCocompact.coCpt | exact GlobalTheory.CompanionTheory.MassCocompact.coCpt | (intros; apply GlobalTheory.CompanionTheory.MassCocompact.coCpt <;> assumption)
end
