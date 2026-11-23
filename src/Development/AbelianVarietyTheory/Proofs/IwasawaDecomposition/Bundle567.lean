module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle470
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LevCmp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar



section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def Eig {V : Type} [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (κ : GAf L n) (c : ℂ) : Prop := ∀ g, F (g * κ) = c • F g

def FrameAut (θ : GAf L n ≃* GAf L n) : Prop :=
  (∀ κ, θ κ ∈ Umax L n ↔ κ ∈ Umax L n) ∧ ∀ v κ, TrivOutside {v} (θ κ) ↔ TrivOutside {v} κ

def cx {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) : J →* ℂˣ := (Units.map e.toMonoidHom).comp χ

theorem cx_apply {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) :
    ((cx e χ κ : ℂˣ) : ℂ) = e (χ κ : Kˣ) := rfl

def LevEq (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (J' : Subgroup (GAf L n)) (χ' : J' →* ℂˣ) : Prop :=
  J = J' ∧ ∀ κ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩

def WtMatch {K : Type} [Field K] (e : K →+* ℂ) {W W' : Type} [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W'),
    ∀ γ, LinearMap.toMatrix b' b' (ρ' γ) = (LinearMap.toMatrix b b (ρ γ)).map e

end Gen

variable {D : D7}

def SideRead (i : D.ntw.Tw) (b : Bool) (k : ℕ) (e : NX.Kk D i k →+* ℂ) : Prop :=
  ∀ x : ↥D.LL0, e (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x)) = embLL0 D x

def ReadsHecke {i : D.ntw.Tw} {k : ℕ} (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E) : Prop :=
  ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofOk D i k)).toMonoidHom).comp ψ) χ


variable (D) in
def GalOf (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) ∧ ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀) χ


variable (D) in
def GPlaces : Prop :=
  (∀ k v, D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) ∧ ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v) ∧
    (∀ u ∈ gPl D, ∃ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.v = u ∧ s.w = D.naut.plGw k v) ∧
    ∃ k, Nonempty (D.nd.PlG k)


variable (D) in
def ParaShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) : Prop :=
  ∀ v ∈ qPl D η, ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
    NG.IsCompAt η s ξ ∧ NG.LevelPara J χ s D.R.r ξ


variable (D) in
def GrpShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) : Prop :=
  NG.IsProdLevel J ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s D.R.r (s.loc _ κ))) ∧
    (∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v →
      ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.UniRT s D.R.r (s.loc _ κ))) ∧
    ∀ κ, TrivOutside (gPl D ∪ qPl D η)ᶜ κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)

abbrev cell (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) :=
  X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA

abbrev eta (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) (v : D.what₂.places.Pl) (j : Fin D.R.m) : HChar D.host.E :=
  cf.mu0 j * xi (D.what₂.muTw v)

abbrev mtAt (M : MtFam D) (v : D.what₂.places.Pl) (j : Fin D.R.m) : MtReal D (D.what₂.muTw v) (j.1 + 1) :=
  M (D.what₂.muTw v) (j.1 + 1) (by omega) (by omega)

def CellWt {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) : Prop := WtMatch e (cell X b hA j).ρ m.wt.ρ

def Joint (η : HChar D.host.E) {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) : Prop :=
  ∃ (θ : GAf D.host.E D.R.nV ≃* GAf D.host.E D.R.nV) (J₁ : Subgroup (GAf D.host.E D.R.nV)) (e : NX.Kk D i k →+* ℂ)
    (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ω : (cell X b hA j).W →ₛₗ[e] V),
    FrameAut θ ∧ SideRead i b k e ∧ Function.Injective ω ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    (∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v →
      ∀ κ, TrivOutside {s.v} κ → NG.UniRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    ∀ κ ∈ J₁, ∃ c c' : ℂ, (∀ x, Eig (m.real x) (θ κ) c) ∧ (∀ f, Eig (fun g => ω (((cell X b hA j).real f).1 g)) (θ κ) c') ∧
      ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → TrivOutside {s.v} κ →
        c ^ (D.host.g kk - 1) = c' ^ (D.host.g kk - 1)

end GlobalTheory.LevCmp

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem GlobalTheory.CommonReading.norm_aut {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem GlobalTheory.CommonReading.norm_aut_le {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (x : Formalism.L2.TwC.intOf l K) : ‖τ x‖ ≤ 1 := by
  rw [GlobalTheory.CommonReading.norm_aut, ← PadicAlgCl.valuation_coe]
  exact_mod_cast x.2.2

namespace GlobalTheory.HeightCounting.SameTw

def Reads (D : D7) (C : NChoice D) (w : D.what₂.places.Pl) {Λ : Type} [Field Λ] (e : D.what₂.LL →+* Λ)
    (φ : D.ntw.O0 (C.twI w) →+* Λ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (τ : Λ →+* Ω) (ι : FractionRing (C.Oe w) →+* Ω),
    (∀ y, τ (φ y) = ι (algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) y)))) ∧
    ∀ x : D.what₂.LL, τ (e x) = ι (C.embW w x)

theorem exists_reads (D : D7) (C : NChoice D) (F : TwFrameC D) {low : Finset ℕ} (hF : TwistFrameLowIndexCompatibility D F low) (w : D.what₂.places.Pl)
    (l : ℕ) [Fact l.Prime] (hl : D.ntw.l (C.twI w) = l) (e : D.what₂.LL →+* PadicAlgCl l)
    (he : ∀ x, 0 ≤ D.what₂.places.val w x ↔ ‖e x‖ ≤ 1) :
    ∃ φ : D.ntw.O0 (C.twI w) →+* PadicAlgCl l, Reads D C w e φ ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
      (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ y, φ y ∈ K) ∧
      ∀ (z : ℤ_[D.ntw.l (C.twI w)]) (z' : ℤ_[l]), HEq z z' →
        φ (algebraMap _ (D.ntw.O0 (C.twI w)) z) = algebraMap ℚ_[l] (PadicAlgCl l) (z' : ℚ_[l]) := by
  subst hl
  haveI := C.Oe_fin w
  obtain ⟨σ, ι, h1, h2⟩ := GlobalTheory.CommonReading.exists_common (C.Oe_inj w)
    ((Subring.subtype _).comp (F.eOk (C.twI w) (C.k' w)).toRingHom)
    (Subtype.val_injective.comp (F.eOk (C.twI w) (C.k' w)).injective)
    (fun y => (F.eOk (C.twI w) (C.k' w) y).2.2) (C.embW w) e fun x => (C.embW_w w x).symm.trans (he x)
  refine ⟨σ.symm.toAlgHom.toRingHom.comp ((Subring.subtype _).comp (F.eO0 (C.twI w)).toRingHom),
    ⟨ℂ_[D.ntw.l (C.twI w)], inferInstance, (algebraMap (PadicAlgCl (D.ntw.l (C.twI w))) ℂ_[D.ntw.l (C.twI w)]).comp
      σ.toAlgHom.toRingHom, ι, fun y => ?_,
      fun x => (h2 x).symm⟩, fun y => ?_, ⟨(F.K0 (C.twI w)).1.map σ.symm.toAlgHom, ?_, fun y => ⟨_, (F.eO0 (C.twI w) y).2.1, rfl⟩⟩, ?_⟩
  · rw [h1]
    refine Eq.trans ?_ ((hF.eOk_alg _ _ _).trans (hF.eO_alg _ y)).symm
    simp
  · exact GlobalTheory.CommonReading.norm_aut_le σ.symm _ (F.eO0 (C.twI w) y)
  · haveI := (F.K0 (C.twI w)).2
    exact LinearEquiv.finiteDimensional (IntermediateField.equivMap _ σ.symm.toAlgHom).toLinearEquiv
  · rintro z _ ⟨⟩
    change σ.symm (F.eO0 (C.twI w) _ : PadicAlgCl _) = _
    rw [hF.ringSpec_baseIntegersEquiv_algebraMap, AlgEquiv.commutes]

theorem Reads.emb {D : D7} {C : NChoice D} (hC : ChoiceC D C) {w : D.what₂.places.Pl} (hw : TwistedAt D w) {Λ : Type} [Field Λ]
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w e φ) (x : D.LL0) (y : D.ntw.O0 (C.twI w))
    (hy : algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y =
      (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x) : e x = φ y := by
  obtain ⟨Ω, _, τ, ι, h1, h2⟩ := h
  apply τ.injective
  rw [h1, h2, hC.emb_side w hw x]
  have : (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) =
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y := by
    rw [hy]; split_ifs <;> rfl
  rw [this, fracOe, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem Reads.of_comp {D : D7} {C : NChoice D} {w : D.what₂.places.Pl} {Λ Λ' : Type} [Field Λ] [Field Λ'] (q : Λ →+* Λ')
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w (q.comp e) (q.comp φ)) : Reads D C w e φ :=
  let ⟨Ω, i, τ, ι, h1, h2⟩ := h
  ⟨Ω, i, τ.comp q, ι, h1, h2⟩

def OneField (D : D7) (C : NChoice D) : Prop :=
  ∀ a : D.nd.Loc, ∃ f : D.ntw.O0 (C.twI (D.nd.w a)) →+* D.nd.O a, HEq f (D.ntw.twist₂ a) ∧
    Reads D C (D.nd.w a) (D.nd.embK a) ((algebraMap (D.nd.O a) (FractionRing (D.nd.O a))).comp f)

def TwReads {D : D7} (C : NChoice D) (X : LocNd (lay0 D)) (T : LocTw X) : Prop :=
  ∀ a : X.nd.Loc, ∃ f : D.ntw.O0 (C.twI (X.nd.w a)) →+* X.nd.O a, HEq f (T.twist₂ a) ∧
    Reads D C (X.nd.w a) (X.nd.embK a) ((algebraMap (X.nd.O a) (FractionRing (X.nd.O a))).comp f)



theorem oneField_withLoc {D : D7} (L : LocAll (lay0 D)) (C : NChoice D) :
    OneField (withLoc L) (chL L C) ↔ TwReads C L.X L.T := Iff.rfl

theorem sameChar_of_inj {O₀ O₁ O₂ Γ Ω : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ] [CommRing Ω]
    (f₁ : O₀ →+* O₁) (f₂ : O₀ →+* O₂) (ψ₁ : Γ →* O₁ˣ) (ψ₂ : Γ →* O₂ˣ) (j₁ : O₁ →+* Ω) (j₂ : O₂ →+* Ω)
    (h₁ : Function.Injective j₁) (h₂ : Function.Injective j₂) (hf : ∀ y, j₁ (f₁ y) = j₂ (f₂ y))
    (hψ : ∀ g, j₁ (ψ₁ g : O₁ˣ) = j₂ (ψ₂ g : O₂ˣ)) : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂ := by
  intro F
  rw [← map_eq_zero_iff j₁ h₁, ← map_eq_zero_iff j₂ h₂]

  simp only [Finsupp.sum, map_sum, map_mul, hf, hψ]

theorem sameTwist_of_oneField (D : D7) (C : NChoice D) (hT : NChTie D C) (h : OneField D C) : GlobalTheory.PtCore.SameTwist D C := by
  intro a
  obtain ⟨f, hf, Ω, _, ιA, ιB, h1, h2⟩ := h a
  obtain ⟨ψ0, -, hw, hl⟩ := hT.psi_eq
  refine (GlobalTheory.PtCore.sameTwistAt_iff D a _ _ _).2 ⟨hT.twOf_eq a, f, hf, ?_⟩
  refine sameChar_of_inj _ _ _ _ (ιA.comp (algebraMap (D.nd.O a) (FractionRing (D.nd.O a))))
    (ιB.comp ((algebraMap (C.Oe (D.nd.w a)) (FractionRing (C.Oe (D.nd.w a)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w a)) (C.k' (D.nd.w a))) (C.Oe (D.nd.w a)))))
    (ιA.injective.comp (IsFractionRing.injective _ _))
    (ιB.injective.comp ((IsFractionRing.injective (C.Oe (D.nd.w a)) _).comp (C.Oe_inj _))) h1 fun g => ?_
  have := h2 ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL)
  rw [hl, hw] at this
  exact this

end GlobalTheory.HeightCounting.SameTw
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem galoisRepsCusp_of_galEx {D : D7} (h : GalEx D) : GlobalTheory.BlockComplement.GaloisRepsCusp D :=
  fun i a ha π hc hr => h (D.nd.l i) (D.naut.iotaQC i) a ha π hc hr


end GlobalTheory.HeightCounting.Up
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.HkCopy

theorem exists_units_copy {T T' Q Q' : Type} {O : T → Type} {O' : T' → Type} [c : ∀ i, CommRing (O i)]
    [c' : ∀ i, CommRing (O' i)] (hT : T = T') (hO : HEq O O') (hc : HEq c c') (hQ : Q = Q')
    (f : ∀ (i : T) (_b : Bool) (_P : Q), (O i)ˣ) :
    ∃ f' : ∀ (i : T') (_b : Bool) (_P : Q'), (O' i)ˣ,
      ∀ (i : T) (i' : T') (b : Bool) (P : Q) (P' : Q'), HEq i i' → HEq P P' → HEq (f' i' b P') (f i b P) := by
  subst hT; cases hO; cases hc; subst hQ
  exact ⟨f, fun i i' b P P' hi hP => by cases hi; cases hP; rfl⟩

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem exists_cHk_copy {D D' : D7} (h : GlobalTheory.TwistChoice.SameExport D D')
    (f : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) :
    ∃ f' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ,
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' →
        HEq (f' i' b P') (f i b P) :=
  exists_units_copy (eq_of_heq h.set.Tw) h.set.O h.set.crO (plE_eq h.gal.R h.gal.host) f

end GlobalTheory.HeightCounting.Up.HkCopy
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameInt

theorem exists_split (D : D7) (PP : HeightOneSpectrum (𝓞 D.host.E)) (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP) :
    ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = PP := by
  refine GlobalTheory.RowUnitProof.exists_splitPlace_eq D PP ?_
  by_contra hs
  refine h fun c hc => ?_
  by_contra hn
  exact hs ⟨c, hc, fun y hy hm => hn ⟨y, hm, hy.trans (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩⟩

theorem frame_of {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0)
    (hF : D.host.F = maximalRealSubfield D.host.E) (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV)
    (hP : R3.StdFrame hF P) (s : T) :
    (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (L.βV k)) ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (L.βV k) s' φ b := by
  have hβ : IsBaseFrame (Vc D k) (L.βV k) (L.ΛV k) 1 := by
    obtain ⟨c, hc⟩ := hL.βV k
    rwa [one_pow] at hc
  refine ⟨fun κ hκ => ?_, fun PP h => ?_⟩
  · have h1 := (hP.2 κ).1 hκ
    exact (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ h1.1).2 h1
  · have hn : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP :=
      h.elim (fun h => GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hL.Pg PP h PP h) fun h => (hL.Q_pl s PP h).2 PP h
    obtain ⟨s', hs'⟩ := exists_split D PP hn
    obtain ⟨φ, b, h1, h2⟩ := GlobalTheory.T.exists_split_reduction_standard_frame_conj D (Vc D k) D.R.nV (GlobalTheory.FrameBlockDiagonal.rankV D k) hF P (L.βV k) (L.ΛV k) hP hβ s'
    exact ⟨s', φ, b, hs', h1, h2⟩

end GlobalTheory.FrameInt

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.LocEx

theorem exists_loc_of_thetaT {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) {v : D.what₂.places.Pl} (hv : TwistedAt D v) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hne : ∃ f, D.what₂.thetaT (D.what₂.muTw v) j f ≠ 0) :
    ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j := by
  obtain ⟨f, hf⟩ := hne
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw v) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hf ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (T.B.V j v) := ⟨⟨_, 0, (T.B.iV_basis j v b).1.ne_zero k⟩⟩
  haveI : Nontrivial (Formalism.L2.heckeAlg T.B j v) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.B j v)
  obtain ⟨i, hi, -⟩ := T.mx_all j v h1 h2 hv I hI
  obtain ⟨ej, ew⟩ := (D.nd.locs_mem _ _ _).1 hi
  exact ⟨i, ew, ej⟩

theorem thetaT_ne_of_lamTr {D : D7} {μ : D.what₂.Tup} {j : ℕ} {σ : D.what₂.FT} (hpos : 0 < DV.lamTr D μ j σ) :
    ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra h
  push_neg at h
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j σ).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) = 0 := by
    ext y
    simp [h _ ((D.what₂.isot j σ).starProjection_apply_mem y)]
  unfold DV.lamTr at hpos
  rw [hT, map_zero, Complex.zero_re, zero_div] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.HeightCounting.Up.LocEx

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def ReadTw (D : D7) (a : D.nd.Loc) : Prop :=
  ∃ (φ : FractionRing (D.ntw.O0 (D.ntw.twOf a)) →+* Qbar (D.ntw.l (D.ntw.twOf a)))
    (ι : Qbar (D.ntw.l (D.ntw.twOf a)) ≃+* ℂ),
    (∀ z : ℤ_[D.ntw.l (D.ntw.twOf a)], φ (algebraMap (D.ntw.O0 (D.ntw.twOf a)) _
        (algebraMap ℤ_[D.ntw.l (D.ntw.twOf a)] (D.ntw.O0 (D.ntw.twOf a)) z)) =
      algebraMap ℚ_[D.ntw.l (D.ntw.twOf a)] (Qbar (D.ntw.l (D.ntw.twOf a))) (z : ℚ_[D.ntw.l (D.ntw.twOf a)])) ∧
    (∀ x : ↥D.LL0, ι (φ ((if D.ntw.twSide a then D.ntw.emb0 (D.ntw.twOf a) else D.ntw.emb0b (D.ntw.twOf a)) x)) =
      embLL0 D x) ∧
    ∀ y : D.ntw.O0 (D.ntw.twOf a), ι (φ (algebraMap _ (FractionRing (D.ntw.O0 (D.ntw.twOf a))) y)) =
      iotaO D.nd D.naut a (D.ntw.twist₂ a y)

end GlobalTheory.RowTriple

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem exists_heq_of_eq {F : D7 → Sort _} {D₁ D₂ : D7} (h : D₁ = D₂) (x : F D₁) : ∃ y : F D₂, HEq y x := by
  subst h; exact ⟨x, HEq.rfl⟩


end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho



end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem heq_cf_of_pack {p q : Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁} (h : p = q) :
    HEq p.2.1 q.2.1 := by
  subst h; rfl


end GlobalTheory.RowTriple.Lay
end
end
