module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringShiftPreservesGoodAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle234
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle166
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle831
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle233
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

@[expose] public section

section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
theorem tame_reciprocity_of_fixed_ne_bot {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (w.adicCompletion E)) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls τ)).tame := by
  obtain ⟨a, ha, ε, H⟩ := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h)
  have hx : GlobalTheory.PRep.fixed (cls τ).rep (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin (cls τ).1)) ≠ ⊥ :=
    GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hf
  obtain ⟨m, b, hb, hw⟩ := haveI := UpperTheory.One.M.charZero_compl w; _root_.UpperTheory.One.M.LawsM.depth H _ (UpperTheory.One.M.good_of_fixed hq _ hx) hx
  rw [← hb, GlobalTheory.WeilDeligne.WD.tame_mk]
  intro g hg
  refine hw g ⟨GlobalTheory.WeilDeligne.Wild_le_Ine hg, fun x hx0 => ?_⟩
  have h1 := hg x hx0
  have e : ((g : G E Ω) x - x) = ((g : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  have h2 : (0 : _) < A.valuation x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx0
  calc A.valuation ((g : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x := by
        exact mul_lt_mul_of_pos_right h1 h2
    _ = A.valuation x := one_mul _
end Loc
end GlobalTheory.RowPar
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
theorem tame_parameter_at_place_of_fixed_ne_bot (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ)
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (s.w.adicCompletion D.host.E)) :
    (_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ s.w).tame := by
  rw [_root_.GlobalTheory.RowPar.parameter_at_place_eq_reciprocity_of_local_component hL D rep σ s τ hτ]
  exact _root_.GlobalTheory.RowPar.tame_reciprocity_of_fixed_ne_bot hL _ τ hf hq
end Loc
end GlobalTheory.RowPar
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
end Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
theorem exists_rowWD_rowTrue_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), RowDepth D rep →
    ∃ Rw : RowWD D, _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep Rw.par Rw.sat := by
  intro hL D rep hD
  refine ⟨⟨_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep, fun σ => satOf (rep σ).S, _root_.GlobalTheory.RowPar.dim_parameter_at_place_eq_rank hL D rep, fun σ k v => ?_⟩, ?_, ?_⟩
  · obtain ⟨s, τ, hs, hl, hf⟩ := hD σ k v
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hq : UpperTheory.One.M.IsQg ((D.naut.plGw k v).adicCompletion D.host.E) := ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩
    rw [← hs] at hq ⊢
    exact _root_.GlobalTheory.RowPar.tame_parameter_at_place_of_fixed_ne_bot hL D rep σ s τ hl hf hq
  · intro σ s τ hτ
    exact _root_.GlobalTheory.RowPar.parameter_at_place_eq_reciprocity_of_local_component hL D rep σ s τ hτ
  · intro σ v w hO Dv hα
    exact satOf_spec (rep σ).S v w hO Dv hα
end GlobalTheory.RowPar
end
end
end
end

section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CovTop.DeepGoodAll
theorem deepGood_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness := by
  intro hP hG hQ hS hT hN
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have P := _root_.GlobalTheory.T.rank_pos_negative_weight_bundle_on_covers hP hG hQ hS hT hN
  unfold _root_.GlobalTheory.CovTop.DeepGoodness _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and P).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, hp1, hq1, hf, hj, hn, hu1, hu2, hs⟩ := hA i hi
  have hpos := hB i hi Y hY
  have hYg := hY.1
  have g := fun s hs' => _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg (wtA (p.κ i)) (p.κ i).n s hn
    (hs s hs').1 (hs s hs').2
  have hon := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg (uM p i) hu1 hu2
  refine ⟨?_, g _ (Or.inl rfl), g _ (Or.inr (Or.inr rfl)), hon.1, hpos, CompFin.finite_comp _ _,
    GlobalTheory.CovTop.good_comp_nonempty _ p.T hL _ hj Y _ _ hYg, hon.2⟩
  have := g 0 (Or.inr (Or.inl rfl))
  rwa [shiftG_zero] at this
end GlobalTheory.CovTop.DeepGoodAll
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.deepGood_of_toroidal_and_semiabelian : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness := by
  first | exact @_root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt_alt | exact _root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem lab_rcAt_ofDet_mul_eq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (ξ η : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (hξ : IsSmoothChar ξ)
    (hη : IsSmoothChar η) (hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → η x = 1) (hξη : IsSmoothChar (ξ * η)) :
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (ξ * η) hξη)) =
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ hξ)) := by
  unfold _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have e1 : LocLanglands.cls (Irr.ofDet 1 (ξ * η) hξη).toIrrRep = (GlobalTheory.LocGL.IrrGL.ofChar ξ hξ).tw η hη := by
    rw [GlobalTheory.LocGL.IrrGL.tw_ofChar]; rfl
  have e2 : LocLanglands.cls (Irr.ofDet 1 ξ hξ).toIrrRep = GlobalTheory.LocGL.IrrGL.ofChar ξ hξ := rfl
  rw [e1, e2, _root_.UpperTheory.One.M.LawsM.twist H _ _ _ (UpperTheory.One.M.good_ofChar ξ hξ), H.one η hη, lpChar_lpOfChar, WD.lab_lpTwist]
  intro σ
  have hd := ha.ord_eq (ineIncl _ σ)
  rw [deg_ineIncl, neg_zero] at hd
  apply hu
  have h0 : Valued.v ((a ((ineIncl _) σ) : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ) :
      HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at hd
  unfold Formalism.L2.Host.IsUnitAt
  rw [← WithZero.exp_log h0, hd, WithZero.exp_zero]
end GlobalTheory.LabFixed
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroLoc
open GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil in
theorem main_m_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n), (∃ v ∈ GlobalTheory.PRep.fixed π.π (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin n)), v ≠ 0) → UpperTheory.One.M.IsQg (w.adicCompletion D.host.E) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w n π).inePol σ = (X - 1) ^ n := by
  intro _ _ hL D w n π ⟨v, hv, hv0⟩ hq σ hσ
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, _, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  have h0 : fixed π.toIrrRep.ρ (KOne (w.adicCompletion D.host.E) (Fin n)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  have h1 := fixed_ne_bot_of_equiv (equivRep π.toIrrRep) h0
  obtain ⟨m, b, hb, hb'⟩ := haveI := UpperTheory.One.M.charZero_compl w; _root_.UpperTheory.One.M.LawsM.depth H (cls π.toIrrRep) (UpperTheory.One.M.good_of_fixed hq _ h1) h1
  have hd := H.dim (cls π.toIrrRep)
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ
  have hW : Formalism.MainNotions.BlochKatoReduction.IsWild (D.nd.plOm.1 w)
      ((ineIncl (D.nd.plOm.2 w) ⟨σ, hI⟩ : Weil (D.nd.plOm.2 w)) : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) := by
    refine ⟨hI, fun y hy => ?_⟩
    have h2 := hσ y hy
    have h3 : (D.nd.plOm.1 w).valuation y ≠ 0 := by simpa using hy
    have e2 : σ y / y - 1 = (σ y - y) / y := by field_simp
    rw [e2, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h3)] at h2
    exact h2
  show (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (cls π.toIrrRep)).inePol σ = (X - 1) ^ n
  rw [← hb] at hd ⊢
  rw [WD.lpDim_mk] at hd
  rw [WD.inePol_of_mem_Ine _ hI, WD.charPol_mk, hb' _ hW, LinearMap.charpoly_one, hd]
end GlobalTheory.DepthZeroLoc
end
end
section
namespace GlobalTheory.DepthZeroTame
end GlobalTheory.DepthZeroTame
end
section
namespace GlobalTheory.DepthZeroType
end GlobalTheory.DepthZeroType
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.One.M.good_cls_of_isLocS_av {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (s : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) s σ) : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ) :=
  GlobalTheory.AVGood.members_good UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz D P.M P.tp.tup P.H.av P.H.level
    (GlobalTheory.AVGood.tameAtG_of_tupTied D P.cf P.tp) i Q s σ hσ
theorem UpperTheory.One.M.cls_eq_of_locV_eq' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E)
    (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' :=
  _root_.UpperTheory.One.M.local_component_class_eq_of_good hL D P i Q Q' sp σ σ' hσ hσ' he (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i Q' sp σ' hσ')
end
section
namespace GlobalTheory.ConjPlaceDual
end GlobalTheory.ConjPlaceDual
end
end
end
