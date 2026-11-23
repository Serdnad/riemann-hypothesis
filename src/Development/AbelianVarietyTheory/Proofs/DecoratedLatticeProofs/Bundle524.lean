module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle504
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle520
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle522
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chainTwistEulerFactorsRestore_proof : ∀ D : D7, Restore D := by
  first | exact @GlobalTheory.ChainTw.restore_holds | exact GlobalTheory.ChainTw.restore_holds | (intros; apply GlobalTheory.ChainTw.restore_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue : ∀ D : D7, SoftQ D → QOfVal D := by
  first | exact @GlobalTheory.LowerBlockParam.qOfVal | exact GlobalTheory.LowerBlockParam.qOfVal | (intros; apply GlobalTheory.LowerBlockParam.qOfVal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a → ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z → ∀ PP ∈ w.Q, ∃ (J : Subgroup (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (μ : Measure (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (ζ : GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → ℂ), IsOpen (J : Set (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧ Integrable ζ μ ∧ (∀ y ∈ J, ζ y = 1) ∧ (∀ g, gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG s.V s.β s.L ↔ GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g ∈ J) ∧ (z = (D.R.t : ℝ) / 2 → ∫ y, ζ y ∂μ = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) ∧ ∀ x ∈ intOff c s, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x = 1 → ∀ y, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) y) = ζ y * flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z x := by
  first | exact @GlobalTheory.ChainTw.OnePlace.local_factor | exact GlobalTheory.ChainTw.OnePlace.local_factor | (intros; apply GlobalTheory.ChainTw.OnePlace.local_factor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedChain_thetaLiftUpSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, LevelLawQ D → UpSpanQ D := by
  first | exact @GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of | exact GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of | (intros; apply GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.transvectionLemma_of_wittCoreDescent : ∀ D : D7, Descent D → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvLemma D := by
  first | exact @GlobalTheory.Unf.transvLemma_of_descent | exact GlobalTheory.Unf.transvLemma_of_descent | (intros; apply GlobalTheory.Unf.transvLemma_of_descent <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem oneCosetBF : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf
  refine ⟨GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf, ?_⟩
  intro h hh hne
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    GlobalTheory.T.iwasawa_decomposition_selfDual_wittSplit_at_place D J.W J.W₀ ρ J.d LW LW₀ v hG.tame hG.sdW hG.sdW₀ hG.monoW h hh
  have h1 := GlobalTheory.T.besselToJacobiFlatMap_support_reduces_to_torus D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have hinv := GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hrat := GlobalTheory.T.torusEntryRatio_integral_at_unramified_place D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hlast := GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hint := GlobalTheory.T.diagonalAdelic_entries_congr_one_of_ratios_at_place D ρ v t ht hinv hrat hlast
  have hK := GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * J.d.emb0 γ, ?_, ?_, J.d.levi t * κ, GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem D J.W LW (· = v) _ _ hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  · exact Subgroup.mul_mem _ hnG (GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt D J.W J.W₀ ρ J.d (· = v) γ hγ)
  · rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.FinPl
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSmallPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def ker {A S X : HSp D} (oma : Om A S) (omX : Om S X) (C : WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ℂ :=
  omX (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0

theorem biLift_eq {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ C h₂ = ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) ∂vS.μ := rfl

section

variable {A S X : HSp D} {χA χS χS' χX : (AE D)ˣ →* Circle} {oma : Om A S} {omX : Om S X}

theorem ker_sum {n : ℕ} (C : Fin n → WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX (∑ i, C i) h₀ h₁ h₂ = ∑ i, ker oma omX (C i) h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (∑ i, C i) u v) 0) = ∑ i, fun v => oma (h₀, h₁) (fun u => C i u v) 0 := by
    funext v
    have e : (fun u => (∑ i, C i) u v) = ∑ i, fun u => C i u v := by
      funext u; simp only [Finset.sum_apply]

    rw [e, map_sum]; simp only [Finset.sum_apply]

  rw [e1, map_sum]; simp only [Finset.sum_apply]

theorem ker_cont (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) :
    Continuous fun x : GA D A × GA D S × GA D X => ker oma omX C x.1 x.2.1 x.2.2 := by
  have := (hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).2.2.2
  exact this.comp (by fun_prop : Continuous fun x : GA D A × GA D S × GA D X =>
    ((x.1, x.2.1), (x.2.1, x.2.2), ((0 : WO A S), (0 : WO S X))))

theorem ker_left (hwa : IsWeilDatumO ψ A S χA χS oma) {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C)
    {γ : GA D A} (hγ : γ ∈ GQ A) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX C (γ * h₀) h₁ h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (γ * h₀, h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((γ * h₀, h₁) : GA D A × GA D S) = (γ, 1) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut γ hγ 1 (one_mem _) _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  rw [e1]

theorem ker_mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {γ : GA D S} (hγ : γ ∈ GQ S) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ (γ * h₁) h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, γ * h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((h₀, γ * h₁) : GA D A × GA D S) = (1, γ) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut 1 (one_mem _) γ hγ _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((γ * h₁, h₂) : GA D S × GA D X) = (γ, 1) * (h₁, h₂) := by simp
  rw [e1, e, map_mul, Module.End.mul_apply, hwX.om_aut γ hγ 1 (one_mem _) _ (hwX.om_pres _ _ hth)]

theorem ker_right (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {δ : GA D X} (hδ : δ ∈ GQ X) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ h₁ (δ * h₂) = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((h₁, δ * h₂) : GA D S × GA D X) = (1, δ) * (h₁, h₂) := by simp
  rw [e, map_mul, Module.End.mul_apply, hwX.om_aut 1 (one_mem _) δ hδ _ (hwX.om_pres _ _ hth)]

theorem inner (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (vA : Vol A) {φ : GA D A → ℂ}
    (hφ : IsContAut A φ) :
    (∀ h₁ h₂, IntegrableOn (fun h₀ => φ h₀ * ker oma omX C h₀ h₁ h₂) vA.𝓕 vA.μ) ∧
      Continuous fun p : GA D S × GA D X => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ p.1 p.2 ∂vA.μ := by
  have hc : Continuous (Function.uncurry fun (g : GA D A) (p : GA D S × GA D X) => φ g * ker oma omX C g p.1 p.2) := by
    show Continuous fun q : GA D A × (GA D S × GA D X) => φ q.1 * ker oma omX C q.1 q.2.1 q.2.2
    exact (hφ.2.comp continuous_fst).mul ((ker_cont hB hwa hwX hC).comp
      (by fun_prop : Continuous fun q : GA D A × (GA D S × GA D X) => (q.1, q.2.1, q.2.2)))
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA (GA D S × GA D X) (fun g p => φ g * ker oma omX C g p.1 p.2) hc
    (fun γ hγ g p => by rw [hφ.1 γ hγ g, ker_left hwa hC hγ])
  exact ⟨fun h₁ h₂ => H.1 (h₁, h₂), H.2.1⟩

theorem mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) :
    (∀ h₂, IntegrableOn (fun h₁ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) vS.𝓕 vS.μ) ∧
      Continuous fun h₂ => biLift oma omX vA vS φ C h₂ := by
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS vS (GA D X) (fun h₁ h₂ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ)
    (inner hB hwa hwX hC hA vA hφ).2 (fun γ hγ g p => by simp only [ker_mid hB hwa hwX hC hγ])
  exact ⟨H.1, H.2.1⟩

theorem outer (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) {T L'' : HSp D} (hT : CoCpt T)
    (vA : Vol A) (vS : Vol S) (vT : Vol T) (o'' : OrthDec X T L'') {φ : GA D A → ℂ} (hφ : IsContAut A φ)
    {F : GA D T → ℂ} (hF : IsContAut T F) :
    IntegrableOn (fun h' => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1))) vT.𝓕 vT.μ := by
  have hc := (mid hB hwa hwX hC hA hS vA vS hφ).2
  have hc' : Continuous fun h' : GA D T => biLift oma omX vA vS φ C (o''.emb (h', 1)) :=
    hc.comp (o''.continuous_emb.comp (by fun_prop : Continuous fun h' : GA D T => ((h', 1) : GA D T × GA D L'')))
  refine (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D T hT vT Unit (fun h' _ => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1)))
    ((hF.2.mul hc').comp continuous_fst) (fun γ hγ g _ => ?_)).1 ()
  have e : ((γ * g, 1) : GA D T × GA D L'') = (γ, 1) * (g, 1) := by simp
  have hδ : o''.emb (γ, 1) ∈ GQ X := o''.emb_mem_GQ hγ (one_mem _)
  rw [hF.1 γ hγ g, e, map_mul, biLift_eq, biLift_eq]
  simp only [ker_right hB hwa hwX hC hδ]

theorem biLift_sum (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : IsContAut A φ) {n : ℕ}
    (C : Fin n → WO A S → WO S X → ℂ) (hC : ∀ i, IsBiTheta ψ A S X (C i)) (h₂ : GA D X) :
    biLift oma omX vA vS φ (∑ i, C i) h₂ = ∑ i, biLift oma omX vA vS φ (C i) h₂ := by
  have e1 : ∀ h₁, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (∑ i, C i) h₀ h₁ h₂ ∂vA.μ =
      ∑ i, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (C i) h₀ h₁ h₂ ∂vA.μ := by
    intro h₁
    simp only [ker_sum, Finset.mul_sum]
    exact integral_finsetSum _ fun i _ => (inner hB hwa hwX (hC i) hA vA hφ).1 h₁ h₂
  rw [biLift_eq]
  simp only [e1]
  rw [integral_finsetSum _ fun i _ => (mid hB hwa hwX (hC i) hA hS vA vS hφ).1 h₂]
  rfl

end

theorem seeSmall : ∀ D : D7, SeeSmall D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ hA hS hT χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hTw hz''
    vA vS vT N Ξ Φ₂ hΞΦ φ F hφ hF
  have hB : BiAct D := GlobalTheory.T.seeSawWeilBiAction_commutes D
  have hSL := GlobalTheory.T.lastSeeSaw_thetaIdentity D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX
    hTw hz''
  have hC : ∀ i, IsBiTheta ψ A S X (lastBi o o'' τ (Ξ i) (Φ₂ i)) := fun i =>
    GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction D ψ h₁.std V₀ A L S X T L'' o o'' τ hτ (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2
  have e0 : (o.resS S).symm (0, 0) = 0 := by rw [← Prod.zero_eq_mk, map_zero]
  have hpt : ∀ i h', biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) (o''.emb (h', 1)) =
      ∫ h in vS.𝓕, omT (h, h') (Φ₂ i) 0 * liftA o om₁ vA φ (Ξ i) h 0 ∂vS.μ := by
    intro i h'
    rw [biLift_eq]
    congr 1
    funext h
    simp only [liftA, e0]
    rw [← integral_const_mul]
    congr 1
    funext h₀
    have key : oma (h₀, h) (fun u' => omX (h, o''.emb (h', 1)) (lastBi o o'' τ (Ξ i) (Φ₂ i) u') 0) 0 =
        omT (h, h') (Φ₂ i) 0 * om₁ (o.emb (h₀, 1), h) (Ξ i) 0 :=
      ((hSL (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2).2 h₀ h h').symm
    have hk := (hB ψ A S X χA χS χS' (χT * χz⁻¹) oma omX ha hX _ (hC i)).2.2.1 (h₀, h) (h, o''.emb (h', 1)) 0 0
    simp only [ker]
    rw [hk, key]
    ring
  have hsum : ∀ h₂, biLift oma omX vA vS φ (∑ i, lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ =
      ∑ i, biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ := fun h₂ =>
    biLift_sum hB ha hX hA hS vA vS hφ (fun i => lastBi o o'' τ (Ξ i) (Φ₂ i)) hC h₂
  simp only [hsum, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => outer hB ha hX (hC i) hA hS hT vA vS vT o'' hφ hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smallPair, hpt]

end GlobalTheory.SeeSmallPf

end
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.contractionOfVacuumCombinations_proof : ∀ D : D7, GlobalTheory.FinPl.ContrOp D := by
  first | exact @GlobalTheory.FinPl.ContrOpProof.contrOp | exact GlobalTheory.FinPl.ContrOpProof.contrOp | (intros; apply GlobalTheory.FinPl.ContrOpProof.contrOp <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.LastTAll D := by
  first | exact @GlobalTheory.LastTAllPf.main | exact GlobalTheory.LastTAllPf.main | (intros; apply GlobalTheory.LastTAllPf.main <;> assumption)
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactAverageProjection_theta_schrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ K : Subgroup (GA D B), IsCompact (K : Set (GA D B)) → ∀ νK : Measure K, IsProbabilityMeasure νK → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsThetaFunO ψ (dblSp A) B (projK om νK φ) ∧ sch ψ A B ν 𝓨 (projK om νK φ) = projS νK (sch ψ A B ν 𝓨 φ) := by
  first | exact @GlobalTheory.RegSchProj.projK_theta_sch | exact GlobalTheory.RegSchProj.projK_theta_sch | (intros; apply GlobalTheory.RegSchProj.projK_theta_sch <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_measure_bound : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j ρ h, GlobalTheory.FinPl.GoodBF (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).B j ρ h) ((commOf (pk W) u (mkGeo m b₀)).J j ρ h) (N₁ j) (M₁ j ρ h) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.Fam.goodBF_of_normalFrames | exact GlobalTheory.Fam.goodBF_of_normalFrames | (intros; apply GlobalTheory.Fam.goodBF_of_normalFrames <;> assumption)
end
