module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle912
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpwardVectorLiftMemRangeCoefficientExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.PlaceRead

variable {D : D7}

abbrev Amb (D : D7) (j : Fin D.R.m) : Type := Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank

section Choice

variable (c : NChoice D) (w : D.what₂.places.Pl)

abbrev KE : Type := FractionRing (c.Oe w)

abbrev chr : G D.host.E D.nd.Om →* (D.ntw.Ok (c.twI w) (c.k' w))ˣ := (c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))

variable {c w}

def viaOk (ι : KE c w →+* ℂ) : D.ntw.Ok (c.twI w) (c.k' w) →+* ℂ := ι.comp (algebraMap _ _)

def ringOf (ι : KE c w →+* ℂ) : Subring ℂ := (ι.comp (algebraMap (c.Oe w) _)).range

def twVia (ρ : Setup D.ntw) (ι : KE c w →+* ℂ) : Twist D Circle :=
  twistOf ρ.rc (viaOk ι) (ρ.ch (c.twI w)) (c.Q w) (chr c w)

def Extends (ρ : Setup D.ntw) (ε : KE c w →+* ℂ) : Prop := viaOk ε = ρ.eOk (c.twI w) (c.sd w) (c.k' w)

theorem Extends.twVia_eq {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) :
    twVia ρ ε = ρ.tw (c.twI w) (c.sd w) (c.k' w) (c.Q w) (chr c w) := by
  rw [twVia, h]; rfl

theorem Extends.apply {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) (a : D.ntw.Ok (c.twI w) (c.k' w)) :
    ε (algebraMap _ _ a) = ρ.eOk (c.twI w) (c.sd w) (c.k' w) a := RingHom.congr_fun h a

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

def rdE (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) : Tgt c w (j.1 + 1) →ₛₗ[ε] Amb D j :=
  let φ : Tgt c w (j.1 + 1) →+ Amb D j := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp (T.rdV (c.k' w) (c.Q w) (chr c w)).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • T.rdV _ _ _ f = ε a • T.rdV _ _ _ (s • f)
      rw [← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) s f, LinearMap.map_smulₛₗ, Algebra.smul_def s a, map_mul, hε.apply,
        smul_smul, mul_comm]
      rfl
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.inductionOn with
      | tmul a f =>
        change ε (s • a) • T.rdV _ _ _ f = ε s • ε a • T.rdV _ _ _ f
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add] }

theorem rdE_tmul (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdE T hε (a ⊗ₜ f) = ε a • T.rdV (c.k' w) (c.Q w) (chr c w) f := rfl


variable (rd) in
def rdF (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) :
    KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →ₛₗ[ε] (GA D (Wc D j) → ℂ) :=
  let φ : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →+ (GA D (Wc D j) → ℂ) := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • rd f = ε a • rd (s • f)
      rw [rd_smul, Algebra.smul_def s a, map_mul, IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply,
        hρ.ek_e, smul_smul, mul_comm]
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.inductionOn with
      | tmul a f =>
        change ε (s • a) • rd f = ε s • ε a • rd f
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add] }

theorem rdF_tmul (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdF rd hρ hε (a ⊗ₜ f) = ε a • rd f := rfl

end Choice

def ConjAt {j : Fin D.R.m} (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ) (τ : ℂ ≃+* ℂ) (F F' : Amb D j) : Prop :=
  ∀ h, ∃ x x' : VsV D j ℂ, ConjVec j τ x x' ∧ F h = Φ x ∧ F' h = Φ ((τ κ / κ) • x')

def intLL (D : D7) : Subring ℂ := (D.what₂.embLL.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)).range

theorem used_of_tw {w : D.what₂.places.Pl} (h : D.what₂.muAt w ≠ D.what₂.mu0) : Used0 D (D.what₂.muTw w) :=
  Or.inr ⟨w, ((D.what₂.muAt_or w).resolve_left h).symm⟩

section Rows

variable {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

def formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) : D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] (X.R.HV j (Y.tupT μ)).H :=
  (LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left ∘ₗ
    (Y.IL.jMt μ hμ j).toLinearMap

theorem extV_formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) :
    X.R.toRealDat.extV j (Y.tupT μ) (formOf Y hμ j x) = (Y.IL.jMt μ hμ j x).1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).apply_symm_apply _)

def fockOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) :
    D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] Amb D j :=
  (X.R.ioP j (PiTensorProduct.tprod ℂ u)).compLeft _ ∘ₗ (X.R.HV j (Y.tupT μ)).e ∘ₗ formOf Y hμ j

theorem fockOf_apply {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (x h) :
    fockOf Y hμ j u x h = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j (Y.tupT μ)).e (formOf Y hμ j x) h) := rfl


variable (X) in
def IsLow (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : (X.R.MW j (sg0 D X.A3.A)).sm τ) = X.geo.v₀ j (sg0 D X.A3.A) τ

variable {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl)
  (j : Fin D.R.m)

abbrev baseOf : Base (Vc D j) (Wc D j) := Z.ρ.B (c.twI w) j (c.sd w)

structure AtPlace : Prop where
  pins : GlobalTheory.Mem.R3.Pins X.R X.F X.cG
  intersectionNumber_baseChange : GlobalTheory.Mem.R3.Holds X.R X.F
  field : FieldOk X
  tw : D.what₂.muAt w ≠ D.what₂.mu0
  ok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)
  cls : ClsQ (D := D) (c.Q w)
  emb : ∀ ε : KE c w →+* ℂ, Extends Z.ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x
  val : ∀ σ, ∃ y : D.what₂.LL, c.embW w y = algebraMap _ (KE c w) ((chr c w σ : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w))
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  ks : (S.A (j.1 + 1)).IsKsForm
  rat : RatRow YS X.geo.v₀ Z.good (c.twI w) j (c.sd w)
  tup : ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
    IsTupOf X.R.toRealDat (baseOf Z c w j) (twVia Z.ρ ι) (Y.tupT (D.what₂.muTw w))

end Rows

end GlobalTheory.PlaceRead

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.TwInputs.HeckePinRead

theorem pull_locE {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] {A : Type} [CommGroup A] (a : Recip D Ω) (ha : a.Good)
    (φ : G D.host.E Ω →* A) (hφ : IsOpen (φ.ker : Set (G D.host.E Ω))) (P : Pl D.host.E) (e : AE D)
    (he : Formalism.L2.JoinChr.IsPlIdem D e P) (k : D.host.Eˣ)
    (hk : Valued.v ((Formalism.L2.Host.atFin P k : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ))
    (x : (AE D)ˣ) (hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E)) (B : ValuationSubring Ω)
    (hB : IsPlaceOver (F := D.host.E) B P) (hine : ∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) (σ : G D.host.E Ω)
    (hσ : IsFrob (F := D.host.E) B (normV P) σ) : a.pull φ x = (φ σ)⁻¹ := by
  have hκ : a.κ (x : AE D) = ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) : Neutral.B1.Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
    rw [hx]; exact ha.loc P e he k
  have hsym : a.sym x = a.art (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
    rw [Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext hκ
  obtain ⟨y, hy, hyσ⟩ := (ha.artin.frob P B hB _).mpr ⟨σ, hσ, rfl⟩
  have hu : Valued.v (((Formalism.L2.Host.atFin P k * y⁻¹ : (P.adicCompletion D.host.E)ˣ)) : P.adicCompletion D.host.E) = 1 := by
    have hy' : Valued.v ((y : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) := hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hk, hy']
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  obtain ⟨τ, hτ, hτu⟩ := (ha.artin.ine P B hB _).mp ⟨_, hu, rfl⟩
  have hs : a.sym x = GlobalTheory.HeckeGal.toAb D.host.E Ω (τ * σ⁻¹) := by
    rw [hsym, show Formalism.L2.Host.atFin P k = (Formalism.L2.Host.atFin P k * y⁻¹) * y by group, map_mul, map_mul, hyσ,
      ← hτu, map_mul]
  rw [a.pull_eq hφ hs, map_mul, hine τ hτ, map_inv, one_mul]

theorem isOpen_ker_psiAt (D : D7) (i : D.ntw.Tw) (b : Bool) :
    IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
  have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext g
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [e]
  exact D.ntw.delta_open i

theorem chi_locU_unif {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (P : PlE D.host)
    (hP : P ∉ D.ntw.S0 i) {e : AE D} (he : Formalism.L2.JoinChr.IsPlIdem D e P) (hee : e * e = e) (σ : G D.host.E D.nd.Om)
    (hσ : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ) :
    (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ) =
      (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)))⁻¹ := by
  rw [hρ.delta i j b]
  have hopen := isOpen_ker_psiAt D i b
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ⁻¹ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ⁻¹)
  have hine : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 P), Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) τ = 1 := by
    intro τ hτ
    have h : D.ntw.delta i τ = 1 := by
      by_contra hne
      exact hP (D.ntw.primes_subset_exceptional i ((D.ntw.delta_ram i P _ (D.nd.plOm.2 P)).1 ⟨τ, hτ, hne⟩))
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h]
  have hpull := pull_locE ρ.rc hρ.rc _ hopen P e he (Formalism.L2.Host.unif P) (Formalism.L2.Host.unif_spec P) _
    (Formalism.L2.JoinChr.locU_val hee _) _ (D.nd.plOm.2 P) hine σ hσ
  change ((charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) _ : Circle) : ℂ) = _
  rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, hpull, unitPart_of_pow hn]
  · simp
  · rw [← map_pow, ← map_inv, ← map_pow, map_pow (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)), hpow, map_one]

def frobU (D : D7) (P : PlE D.host) : G D.host.E D.nd.Om :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose

theorem frobU_spec (D : D7) (P : PlE D.host) : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) (frobU D P) :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose_spec.2

def uD (D : D7) : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ := fun i b P =>
  Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) (frobU D P))

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}

theorem isDeltaInv_uD {D : D7} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hpin : RealPin Rl cG ρ) : IsDeltaInv ρ (uD D) := by
  intro i j b k P hk α z hα hz
  obtain ⟨-, -, hsp, hP⟩ := hk
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hsp hP
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hdQ.1
  have hee : e * e = e := he.1.1
  have h1 := (hpin.delta i j b).2 P e (GlobalTheory.HeckeDetChar.isPlIdem he) (Formalism.L2.Host.unif P) _
    (Formalism.L2.JoinChr.locU_val hee (Formalism.L2.Host.unif P))
  have h2 := chi_locU_unif hρ i j b P hP (GlobalTheory.HeckeDetChar.isPlIdem he) hee (frobU D P) (frobU_spec D P)
  rw [GlobalTheory.HeckeDetChar.chi_detAt (hpin.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ hα hz,
    show (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) = (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ)
      from h1.symm, h2, inv_pow, inv_inv]
  rfl

end GlobalTheory.TwInputs.HeckePinRead

namespace GlobalTheory.TwInputs

end GlobalTheory.TwInputs
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacFixOpen



theorem exists_open_fix_vacO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → T.SigOK →
    ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J → om (x, 1) f₀ = f₀ := by
  intro D ψ θ S T χS χT om hW hSs hTs sS sT hcS hcT ΛS ΛT hsdS hsdT f₀ hvac
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D S => ((x, (1 : GA D T)) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const :
      Continuous fun x : GA D S => ((x, (1 : GA D T)) : GA D S × GA D T))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial x →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n₁.factorial k → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, 1) f₀ = c • f₀ := by
    intro k hk hc
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        fun _ => True), u = actO S T k 1 u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ 1 u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D T) u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ k 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.one_mul, Matrix.mul_one])
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one T θ τ (sT τ)) hΛ f₀ hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ S T sS sT hSs hTs hcS hcT ΛS ΛT hsdS hsdT f₀ _ hvac hvac'
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D S => om (k, 1) f₀ w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_id.prodMk continuous_const)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k → om (k, 1) f₀ = f₀ := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, 1) f₀ = c • f₀ ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (GlobalTheory.SmoothVac.om_pow_eq om (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : om ((1 : GA D S), (1 : GA D T)) f₀ w₀ = f₀ w₀ := by
      show om 1 f₀ w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖f₀ w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (f₀ w₀)]
  obtain ⟨n, hn⟩ := key
  have hN : 0 < n₁.factorial * n.factorial := Nat.mul_pos n₁.factorial_pos n.factorial_pos
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial)).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S hN, fun k hk hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S k := congrArg Subtype.val e
  refine hn k hk ?_
  have hc := hk'.2
  unfold GlobalTheory.Member.FinCong at hc ⊢
  rw [← e']
  exact hc

end GlobalTheory.VacFixOpen
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.fockPolynomial_lieDerivative_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (ψ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) → (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ' ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ' w'))) := by
  first | exact @GlobalTheory.LieEquivFock.lie_equivariant | exact GlobalTheory.LieEquivFock.lie_equivariant | (intros; apply GlobalTheory.LieEquivFock.lie_equivariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

theorem _root_.GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H), ∃ u : (R.HV i t).H, R.extV i t u = upVec R i t v b y := by
  first | exact @GlobalTheory.AdjRange.upVec_mem_range | exact GlobalTheory.AdjRange.upVec_mem_range | (intros; apply GlobalTheory.AdjRange.upVec_mem_range <;> assumption)
end
