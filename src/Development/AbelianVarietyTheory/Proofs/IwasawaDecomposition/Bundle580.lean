module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle562
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem galOf_of_orderDvd : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  intro hGAR D χ n hn hχ hz
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles D.host.E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles D.host.E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing D.host.E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab D.host.E D.nd.Om →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  let r : G D.host.E D.nd.Om →* ℂˣ := c.comp (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
  have hrc : Continuous r := hcc.comp continuous_quot_mk
  have hrn : ∀ g, r g ^ n = 1 := fun g => by
    obtain ⟨x, hx⟩ := ha.quot.surjective (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om g)
    show c _ ^ n = 1
    rw [← hx, hc, h1]
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hrc hn hrn
  obtain ⟨z, hz⟩ := hz
  obtain ⟨ψ, hψ⟩ := GlobalTheory.TwistChoice.exists_char_descent D.what₂.embLL hn hz r hrn
  have hψr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ = r := MonoidHom.ext fun g => Units.ext (hψ g)
  have hker : ψ.ker = r.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    rw [← hψr, MonoidHom.comp_apply]
    constructor
    · intro h; rw [h, map_one]
    · intro h
      apply Units.ext
      apply D.what₂.embLL.injective
      have := congrArg Units.val h
      simpa using this
  refine ⟨ψ, ⟨by rw [hker]; exact hro, art, ha, ?_⟩, fun g => ?_⟩
  · rw [hψr]
    intro x σ hσ
    show χ.1 x = c (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ)
    rw [← hσ, hc]
  · apply Units.ext
    apply D.what₂.embLL.injective
    have := congrArg Units.val (hrn g)
    rw [← hψr] at this
    simpa using this

end GlobalTheory.LevCmp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

theorem sameGalois_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂} (h : SameGalois N N') :
    SameGalois N' N := ⟨h.R.symm, h.host.symm, h.loc.symm, h.Om.symm, h.instOm.symm, h.algOm.symm, h.plOm.symm, h.PlG.symm⟩

theorem twistDataAgreeAcrossCoefficients_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'} (h : TwistDataAgreeAcrossCoefficients X X') : TwistDataAgreeAcrossCoefficients X' X :=
  ⟨h.cc.symm, h.Tw.symm, h.l.symm, h.O0.symm, h.crO0.symm, h.algO0.symm, h.topO0.symm, h.O.symm, h.crO.symm, h.algO.symm, h.Ok.symm, h.crOk.symm, h.algOk.symm, h.zk.symm, h.pD.symm, h.chi1.symm, h.Sig.symm, h.finSig.symm, h.jS.symm, h.side.symm, h.rhoS.symm, h.S0.symm, h.hEig.symm, h.abelian₂.symm, h.sideL.symm, h.RCG.symm, h.grpRCG.symm, h.finRCG.symm, h.art.symm, h.th.symm⟩

theorem sameForms_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'} (h : SameForms Y Y') :
    SameForms Y' Y :=
  ⟨h.Fm.symm, h.acgFm.symm, h.modFmK.symm, h.modFmO.symm, h.actG.symm, h.U.symm, h.psiU.symm, h.eAlg.symm, h.Dat.symm, h.th.symm, h.lev.symm, h.thPsi.symm, h.MtV.symm, h.acgMt.symm, h.modMtK.symm, h.modMtO.symm, h.MtLat.symm, h.thP.symm, h.hkF.symm⟩

theorem heq_app {α α' β β' : Type} (hα : α = α') (hβ : β = β') {f : α → β} {f' : α' → β'} (hf : HEq f f') {x : α} {x' : α'}
    (hx : HEq x x') : HEq (f x) (f' x') := by
  subst hα; subst hβ
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hx
  rfl

theorem move_set {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂} (h1 : SameGalois N N')
    (B' : Finset (PlE D'.host)) : ∃ B : Finset (PlE D.host), HEq B B' ∧
      ∀ (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → Disjoint Q B → Disjoint Q' B' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2
  exact ⟨B', HEq.rfl, fun Q Q' hQ h => by obtain rfl := eq_of_heq hQ; exact h⟩



set_option maxRecDepth 100000 in
theorem move_pack {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'} (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X')
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') {Q : Finset (PlE D.host)} {k : ℕ} (ψ : X.RCG i Q →* (X.Ok i k)ˣ) :
    ∃ (Q' : Finset (PlE D'.host)) (ψ' : X'.RCG i' Q' →* (X'.Ok i' k)ˣ), HEq Q Q' ∧ ∀ a : ℤ, HEq (ψ ^ a) (ψ' ^ a) := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hi
  exact ⟨Q, ψ, HEq.rfl, fun _ => HEq.rfl⟩



set_option maxRecDepth 100000 in
theorem move_xd {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y') (m : ℕ)
    (x0 : ∀ i j b, Set (Y.Dat i j b))
    (hP : ∀ i j b, ∀ a ∈ x0 i j b, ∀ u : Y.U, Y.actG i j b u (Y.th i j b a) =
      ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • Y.th i j b a)
    (N0 : X.Tw → ℕ) (S : ∀ i j b, Finset (Y.Dat i j b)) :
    ∃ x0' : ∀ i j b, Set (Y'.Dat i j b), (∀ i j b, ∀ a ∈ x0' i j b, ∀ u : Y'.U, Y'.actG i j b u (Y'.th i j b a) =
      ((Y'.psiU i b u : (FractionRing (X'.O i))ˣ) : FractionRing (X'.O i)) • Y'.th i j b a) ∧ HEq x0 x0' ∧
      ((∀ i j b, 1 ≤ j → j ≤ m → x0 i j b = Set.univ) → ∀ i j b, 1 ≤ j → j ≤ m → x0' i j b = Set.univ) ∧
      (∃ N0' : X'.Tw → ℕ, HEq N0 N0') ∧ ∃ S' : ∀ i j b, Finset (Y'.Dat i j b), HEq S S' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  exact ⟨x0, hP, HEq.rfl, id, ⟨N0, HEq.rfl⟩, S, HEq.rfl⟩

end GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

namespace GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

theorem exists_disjoint_choice {α ι : Type} [DecidableEq α] {Z : ι → Type} (c : ∀ i, Z i → Finset α) (P : ∀ i, Z i → Prop)
    (h : ∀ i (B : Finset α), ∃ z, P i z ∧ Disjoint (c i z) B) (T : Finset ι) :
    ∃ f : ∀ i, Z i, (∀ i, P i (f i)) ∧ ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → Disjoint (c i (f i)) (c i' (f i')) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    choose f hf using fun i => h i ∅
    exact ⟨f, fun i => (hf i).1, by simp⟩
  | insert a T ha ih =>
    obtain ⟨f, hf, hf'⟩ := ih
    obtain ⟨z, hz, hz'⟩ := h a (T.biUnion fun i => c i (f i))
    have key : ∀ i ∈ T, Disjoint (c a (Function.update f a z a)) (c i (Function.update f a z i)) := fun i hi => by
      rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hi)]
      exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem (fun i => c i (f i)) hi) hz'
    refine ⟨Function.update f a z, fun i => ?_, fun i hi i' hi' hne => ?_⟩
    · by_cases hi : i = a
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hf i
    · rcases Finset.mem_insert.1 hi with h1 | h1 <;> rcases Finset.mem_insert.1 hi' with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · subst h1; exact key i' h2
      · subst h2; exact (key i h1).symm
      · rw [Function.update_of_ne (by rintro rfl; exact ha h1), Function.update_of_ne (by rintro rfl; exact ha h2)]
        exact hf' i h1 i' h2 hne

theorem epsilon_congr {β : Type} {p q : β → Prop} (h1 h2 : Nonempty β) (h : p = q) :
    @Classical.epsilon _ h1 p = @Classical.epsilon _ h2 q := by
  subst h; rfl

end GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

namespace GlobalTheory.HeightCounting.Up


open GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations in

theorem nonempty_seed_of_kept : ∀ (D₁ D₀ : D7) (C₁ : NChoice D₁) (C₀ : NChoice D₀) (xd : ThData D₀), Kept C₁ C₀ → D₁.what₂.places.Pl = D₀.what₂.places.Pl → (∀ v v₀, HEq v v₀ → TwistedAt D₁ v → TwistedAt D₀ v₀) → NChTie D₁ C₁ → (∀ v, C₁.twI (D₁.what₂.places.conj v) = C₁.twI v) → {v | TwistedAt D₁ v}.Finite → IsGalois ℚ ↥D₁.LL0 → (∀ v, TwistedAt D₀ v → D₀.ntw.NonzeroIndexPlace (C₀.twI v)) → ExportAt D₀ C₀ xd → XdAll xd → ∀ A, Nonempty (Seed D₁ A) := by
  intro D₁ D₀ C₁ C₀ xd hK hPl htw hT hc hfin hG hW hE hX A
  classical
  have g1 := sameGalois_symm hK.gal
  have g2 := twistDataAgreeAcrossCoefficients_symm hK.set
  have g3 := sameForms_symm hK.forms
  obtain ⟨N0, S, hp, hs⟩ := hE
  obtain ⟨x1, hx1P, hxd, hxall, ⟨N1, hN⟩, S1, hS⟩ := move_xd g1 g2 g3 D₀.R.m xd.xd0 xd.thetaBase_invariant_action N0 S
  let xd₁ : ThData D₁ := ⟨x1, hx1P⟩
  have hm : D₁.R.m = D₀.R.m := by rw [hK.gal.R]
  have hall : XdAll xd₁ := fun i j b h1 h2 => hxall hX i j b h1 (hm ▸ h2)
  have hTw : D₀.ntw.Tw = D₁.ntw.Tw := eq_of_heq g2.Tw
  obtain ⟨-, -, -, -, hb⟩ := same_basic g1 g2 g3
  have key : ∀ r, TwistedAt D₁ r → TwIn.Ok (⟨twEOf xd₁, N1, S1⟩ : TwIn D₁) (C₁.twI r) ∧
      ∀ B : Finset (PlE D₁.host), ∃ (Q : Finset (PlE D₁.host)) (k : ℕ)
        (ψ : D₁.ntw.RCG (C₁.twI r) Q →* (D₁.ntw.Ok (C₁.twI r) k)ˣ), ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (C₁.twI r)) →
          IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 (C₁.twI r) (twEps D₁ (C₁.twI r)) (S1 (C₁.twI r)) B Q k (ψ ^ a) := by
    intro r hr
    have hr₀ : TwistedAt D₀ (cast hPl r) := htw r (cast hPl r) (cast_heq hPl r).symm hr
    have hii : HEq (C₀.twI (cast hPl r)) (C₁.twI r) := heq_app hPl.symm hTw hK.twI.symm (cast_heq hPl r)
    obtain ⟨hl, hSS, -⟩ := hb _ _ hii
    obtain ⟨hSet, hOk⟩ := hs _ hr₀
    refine ⟨?_, fun B => ?_⟩
    · have h9 := fun j (hj : j ∈ Finset.Icc 1 D₁.R.m) b => fullRk_basisOf_transfer g1 g2 g3 (E := twEOf xd) (E' := twEOf xd₁)
        hxd hii j b ((hSS S S1 hS).2 j b) ⟨hOk.1 j (hm ▸ hj) b, hOk.2 j (hm ▸ hj) b⟩
      exact ⟨fun j hj b => (h9 j hj b).1, fun j hj b => (h9 j hj b).2⟩
    · obtain ⟨B₀, hB, -⟩ := move_set g1 B
      obtain ⟨Q₀, k, ψ₀, hG0⟩ := hp _ (hW _ hr₀) hSet _ (twEps_pos _ _) hOk.1 (S (C₀.twI (cast hPl r))) hOk.2 B₀
      obtain ⟨Q₁, ψ₁, hQ, hψ⟩ := move_pack g1 g2 hii ψ₀
      refine ⟨Q₁, k, ψ₁, fun a ha => ?_⟩
      have he : twEps D₁ (C₁.twI r) = twEps D₀ (C₀.twI (cast hPl r)) := by rw [twEps, twEps, hl]
      have ha' : IsCoprime a (D₀.ntw.l (C₀.twI (cast hPl r)) : ℤ) :=
        Int.isCoprime_iff_gcd_eq_one.2 (by rw [hl]; simpa [Int.gcd] using ha)
      rw [he]
      exact goodTw_transfer g1 g2 g3 (B := BlochKatoReduction.bk0 D₀) (B' := BlochKatoReduction.bk0 D₁) hK.br.symm rfl rfl hxd hN hii _
        (hSS S S1 hS).1 hB hQ k (hψ a) (hG0 a ha')
  let rep : D₁.what₂.places.Pl → D₁.what₂.places.Pl := fun v =>
    @Classical.epsilon _ ⟨v⟩ fun r => TwistedAt D₁ r ∧ OverOnePair D₁ v r
  have hrep : ∀ v, TwistedAt D₁ v → TwistedAt D₁ (rep v) ∧ OverOnePair D₁ v (rep v) := fun v hv =>
    Classical.epsilon_spec (p := fun r => TwistedAt D₁ r ∧ OverOnePair D₁ v r) ⟨v, hv, overOnePair_refl v⟩
  have hrep_eq : ∀ v v', OverOnePair D₁ v v' → rep v' = rep v := fun v v' h =>
    epsilon_congr _ _ (funext fun r => propext ⟨fun ⟨h1, h2⟩ => ⟨h1, h.trans hG h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (h.symm hG).trans hG h2⟩⟩)
  let s : D₁.what₂.places.Pl → D₁.ntw.Tw := fun v => if TwistedAt D₁ v then C₁.twI (rep v) else C₁.twI v
  have hs_tw : ∀ v, TwistedAt D₁ v → s v = C₁.twI (rep v) := fun v hv => if_pos hv
  have hs_un : ∀ v, ¬ TwistedAt D₁ v → s v = C₁.twI v := fun v hv => if_neg hv
  let P : ∀ i : D₁.ntw.Tw, (Σ (Q : Finset (PlE D₁.host)) (k : ℕ), D₁.ntw.RCG i Q →* (D₁.ntw.Ok i k)ˣ) → Prop :=
    fun i z => ∀ r, TwistedAt D₁ r → C₁.twI r = i → ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l i) →
      IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 i (twEps D₁ i) (S1 i) (A i) z.1 z.2.1 (z.2.2 ^ a)
  have hch : ∀ i (B : Finset (PlE D₁.host)), ∃ z, P i z ∧ Disjoint z.1 B := by
    intro i B
    by_cases hex : ∃ r, TwistedAt D₁ r ∧ C₁.twI r = i
    · obtain ⟨r, hr, rfl⟩ := hex
      obtain ⟨Q, k, ψ, hq⟩ := (key r hr).2 (A (C₁.twI r) ∪ B)
      refine ⟨⟨Q, k, ψ⟩, fun r' _ _ a ha => (goodTw_union (hq a ha)).1, ?_⟩
      have h1 := (goodTw_union (hq 1 (by simp))).2
      exact h1
    · exact ⟨⟨∅, 0, 1⟩, fun r hr he => absurd ⟨r, hr, he⟩ hex, Finset.disjoint_empty_left _⟩
  obtain ⟨f, hf, hf'⟩ := exists_disjoint_choice (Z := fun i => Σ (Q : Finset (PlE D₁.host)) (k : ℕ),
    D₁.ntw.RCG i Q →* (D₁.ntw.Ok i k)ˣ) (fun _ z => z.1) P hch (hfin.toFinset.image s)
  have goodAt : ∀ i, (∃ r, TwistedAt D₁ r ∧ C₁.twI r = i) → TwIn.Ok (⟨twEOf xd₁, N1, S1⟩ : TwIn D₁) i ∧
      ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l i) →
        IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 i (twEps D₁ i) (S1 i) (A i) (f i).1 (f i).2.1 ((f i).2.2 ^ a) := by
    rintro i ⟨r, hr, rfl⟩
    exact ⟨(key r hr).1, hf _ r hr rfl⟩
  have hmem : ∀ v, TwistedAt D₁ v → s v ∈ hfin.toFinset.image s := fun v hv =>
    Finset.mem_image_of_mem s (hfin.mem_toFinset.2 hv)
  refine ⟨⟨s, fun v => ?_, fun v => ?_, fun v v' hv hv' ho => ?_, xd₁, hall, N1, S1, fun i => (f i).1, fun i => (f i).2.1,
    fun i => (f i).2.2, fun v hv => goodAt (s v) ⟨rep v, (hrep v hv).1, (hs_tw v hv).symm⟩,
    fun v v' hv hv' hne => hf' _ (hmem v hv) _ (hmem v' hv') hne⟩⟩
  · by_cases hv : TwistedAt D₁ v
    · rw [hs_tw v hv]
      exact ReadsAt.of_pair hG (readsAt_of_tie hT (rep v)) ((hrep v hv).2.symm hG)
    · exact ⟨C₁.sd v, by rw [hs_un v hv]; exact readsAt_of_tie hT v⟩
  · by_cases hv : TwistedAt D₁ v
    · rw [hs_tw v hv, hs_tw _ ((twistedAt_conj D₁ v).2 hv), hrep_eq v _ (overOnePair_conj v)]
    · rw [hs_un v hv, hs_un _ (fun h => hv ((twistedAt_conj D₁ v).1 h)), hc v]
  · rw [hs_tw v hv, hs_tw v' hv', hrep_eq v v' (Or.inl ho)]

end GlobalTheory.HeightCounting.Up
end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar




section Gen

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}


variable (R) in
def EigVec (i : Fin D.R.m) (k : ℕ) (Q : PlE D.host) (Rr : Finset (GA D (Wc D i))) (c : ↥D.LL0) (v : (R.HW i (sg0 D A3.A)).H) : Prop :=
  hkNorm R i k Q • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e v) =
    D.what₂.embLL ((c : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e v

theorem eigAd_iff_eigVec (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : EigAd Y Sb eig ↔
    ∀ (i : Fin D.R.m) σ k Q α Rr, HkDat R Sb i k Q α Rr → D.nd.goodRow σ → ∀ y ∈ D.what₂.isot (i.1 + 1) σ,
      EigVec R i k Q Rr (eig (i.1 + 1) σ k Q) (Y.mj.eW i y) := Iff.rfl

theorem EigVec.congr {i : Fin D.R.m} {k : ℕ} {Q : PlE D.host} {Rr : Finset (GA D (Wc D i))} {c : ↥D.LL0}
    {v v' : (R.HW i (sg0 D A3.A)).H} (h : EigVec R i k Q Rr c v) (e : HEq v' v) : EigVec R i k Q Rr c v' := eq_of_heq e ▸ h

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))

theorem eigVec_loc {i k Q Rr c v} (h : EigVec x.m.z.R i k Q Rr c v) :
    EigVec (datL x L).R i k Q Rr c v := by
  with_unfolding_all exact h

end GlobalTheory.HeightCounting.Fin3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem GlobalTheory.HeckeLocN.exists_twRing_of_large : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  intro D C F low E0 hT hC w
  obtain ⟨φ, hR, hn, ⟨K, hKf, hK⟩, halg⟩ :=
    GlobalTheory.HeightCounting.SameTw.exists_reads D C F hT w (D.what₂.places.resChar w) (C.twI_l w) (E0.emb w) (E0.emb_w w)
  refine ⟨⟨K, hKf⟩, ?_⟩
  intro X j hXE hle
  let g : D.ntw.O0 (C.twI w) →+* ↥(X.Kx j w).1 := φ.codRestrict (X.Kx j w).1 (fun y => hle (hK y))
  let f : D.ntw.O0 (C.twI w) →+* OcC X j w :=
    g.codRestrict (Loc.OL (X.Kx j w)) (fun y => (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) (g y)).2 (hn y))
  have hf : ∀ y, iqC X j w (algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) = φ y := fun y => by
    rw [iqC_alg]; rfl
  have e1 : (iqC X j w).comp (ecC X j w) = E0.emb w := by
    ext x; rw [RingHom.comp_apply, iqC_ec, hXE]
  have e2 : (iqC X j w).comp ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) = φ := by
    ext y; exact hf y
  have hRd : GlobalTheory.HeightCounting.SameTw.Reads D C w (ecC X j w) ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) :=
    GlobalTheory.HeightCounting.SameTw.Reads.of_comp (iqC X j w) (by rw [e1, e2]; exact hR)
  refine ⟨f, ?_, hRd, fun hw x y hy => GlobalTheory.HeightCounting.SameTw.Reads.emb hC hw hRd x y hy⟩
  intro z z' hz
  apply Subtype.val_injective
  apply Subtype.val_injective
  change φ _ = _
  rw [halg z z' hz]
  rfl
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatHeckeBall


end GlobalTheory.RatHeckeBall
end
