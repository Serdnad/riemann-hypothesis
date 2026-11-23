module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle880
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle926
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle876
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle922
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TwInputs.AtLayer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar




section General

variable {D : D7}

theorem injective_of_cellTie {ρ : Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) : Function.Injective rd := by
  refine (injective_iff_map_eq_zero rd).2 fun x hx => ?_
  have h1 : ((1 : D.ntw.Ok i 0) ⊗ₜ[D.ntw.O i] x : D.ntw.Ok i 0 ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) = 0 :=
    T.injective_rdK 0 (by rw [rdK_tmul, hx, smul_zero, map_zero])
  haveI : Module.Flat (D.ntw.O i) (FractionRing (D.ntw.O i)) := IsLocalization.flat _ (nonZeroDivisors (D.ntw.O i))
  haveI : Module.Flat (D.ntw.O i) (D.nexp.Fm i ((j : ℕ) + 1) b) :=
    Module.Flat.trans (D.ntw.O i) (FractionRing (D.ntw.O i)) _
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := D.nexp.Fm i ((j : ℕ) + 1) b)
    (Algebra.linearMap (D.ntw.O i) (D.ntw.Ok i 0)) (D.ntw.Ok_inj i 0)
  have h3 : ((1 : D.ntw.O i) ⊗ₜ[D.ntw.O i] x : D.ntw.O i ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) = 0 := h2 (by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one, h1, map_zero])
  simpa using congrArg (TensorProduct.lid (D.ntw.O i) _) h3

def IsFrobUnit (D : D7) (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) : Prop :=
  ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    u i b P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹)

theorem exists_hecke (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j))
    (h0 : ∀ j P, hL j 0 P = 1) (hr : GlobalTheory.ExportPin.Reads X.R X.cG S YS hL)
    (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) (hu : IsFrobUnit D u)
    (hz : ∀ i j b P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j b 0 P x = x) :
    ∃ H : NExpRealH X.R X.cG S YS, GlobalTheory.ExportPin.Reads X.R X.cG S YS H.hL ∧
      ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (algebraMap (D.ntw.O0 i) (D.ntw.O i)
          ((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  have hδ : IsDeltaInv Z.ρ u := by
    intro i j b k P hk α z hα hz
    have e : u i b P = HeckePinRead.uD D i b P := by
      rw [hu i b P hk.2.2.2 _ (HeckePinRead.frobU_spec D P)]
      cases b <;> rfl
    rw [e]
    exact HeckePinRead.isDeltaInv_uD Z.good Z.pin i j b k P hk α z hα hz
  refine ⟨⟨hL, hs, fun i b k P => (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k,
    fun _ _ _ => pow_zero _, fun i b P => ((u i b P).isUnit.map _).pow 1, fun i b k P => by rw [pow_one], ?_⟩, hr, ?_⟩
  · intro i j b h1 h2 k P x hP hsp hk
    rcases Nat.eq_zero_or_pos k with rfl | k1
    · rw [hz i j b P x h1 h2 hP hsp, pow_zero, one_smul,
        (GlobalTheory.ExportPin.Model.hkFR_of_smul S i j b (hs j h1 h2) 0 P).2 (h0 j P)]
      rfl
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      let j' : Fin D.R.m := ⟨n, h2⟩
      have hk' : HkIdx i k P := ⟨k1, hk, hsp, hP⟩
      obtain ⟨α, R, z, d⟩ := GlobalTheory.HeckeDatumExists.exists_isHeckeDatum D _ _ Z.ρ Z.good i j' b k P hk'
      have e := (Z.hecke i j' b).eq (injective_of_cellTie (Z.tie i j' b)) hk' d
        (heckeAt_of_scaled YS X.geo.v₀ Z.pin X.char.lev X.char.allPl Z.good hr hδ i j' b (Z.ν i j' b)
          (hs _ (Nat.le_add_left _ _) j'.2) hk' (f := x) ((YS.eF i _ b (Nat.le_add_left _ _) j'.2).apply_symm_apply _))
      exact (congrArg (YS.eF i _ b h1 h2) e).trans ((YS.eF i _ b h1 h2).apply_symm_apply _)
  · intro i b P hP σ hσ
    change (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ 1 = _
    rw [pow_one, hu i b P hP σ hσ, Units.coe_map]
    rfl

theorem hkF_zero_of_sideB {cf Rw low Pq S hL eig θ} (Bs : SideB D cf Rw low Pq S hL eig θ) (h0 : ∀ j P, hL j 0 P = 1) :
    ∀ i j b P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j b 0 P x = x := by
  intro i j b P x h1 h2 hP hsp
  refine (Bs.eF i j b h1 h2).injective ?_
  rw [Bs.hkEq i j b h1 h2 0 P x hP hsp (Nat.zero_le _), pow_zero, one_smul]
  exact LinearMap.congr_fun ((GlobalTheory.ExportPin.Model.hkFR_of_smul S i j b (Bs.hs j h1 h2) 0 P).2 (h0 j P)) _

end General

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : NCore hL t n}

end Rows

end GlobalTheory.TwInputs.AtLayer

namespace GlobalTheory.TwInputs.AtLayer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

end GlobalTheory.TwInputs.AtLayer

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.GalLoc.PsiLvl

def PsiRead (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i true ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
        (D.ntw.emb0 i ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0))

theorem exists_theta_of_eq {D₀ : D7} {L : LocAll (lay0 D₀)} {D' : D7} (h : D' = withLoc L)
    (θ0 : ∀ kk : Fin 2, Multiplicative (ZMod ((withLoc L).host.g kk)) →* (↥(withLoc L).LL0)ˣ)
    (h0 : PsiRead (withLoc L) θ0) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ, HEq θ θ0 ∧ PsiRead D' θ := by
  subst h
  exact ⟨θ0, HEq.rfl, h0⟩

end GlobalTheory.GalLoc.PsiLvl
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_open_subgroup_fix_vacuum_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ M : ℕ, M ≠ 0 → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ k ∈ GfC V, fin V k ∈ J → ∀ y : WO V W, M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → om (k, 1) (heisO ψ V W y f₀) = heisO ψ V W y f₀ := by
  first | exact @GlobalTheory.VacTransFix.fix_trans | exact GlobalTheory.VacTransFix.fix_trans | (intros; apply GlobalTheory.VacTransFix.fix_trans <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.movedVacuum_translateSum_flipScalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (x : (AE D)ˣ) (lam : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → Y.card = flipIdx V W T m → om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ → lam = flipScal χW V W T m x := by
  first | exact @GlobalTheory.FlipScal.moved_vacuum_factor | exact GlobalTheory.FlipScal.moved_vacuum_factor | (intros; apply GlobalTheory.FlipScal.moved_vacuum_factor <;> assumption)
end

section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay
open scoped ComplexConjugate nonZeroDivisors ENNReal
open GlobalTheory.RSTheta GroundTheory.Global.IdeleGroup

namespace GlobalTheory.RSThetaM

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def measSub (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Measurable F}
  add_mem' hF hG := Measurable.add hF hG
  zero_mem' := measurable_const
  smul_mem' c _ hF := Measurable.const_smul hF c

theorem measurable_gl_of_matrix {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (h : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) : Measurable γ := by
  have hu : Continuous fun q : invSet E a =>
      (IsUnit.unit (q.2 : IsUnit (Matrix.of q.1)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have := GlobalTheory.ConstTermSmooth.contDiffOn_invM.continuousOn.comp_continuous
      (f := fun q : invSet E a => q.1) continuous_subtype_val fun q => q.2
    refine Continuous.congr this fun q => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  have hm : Measurable fun x => (⟨toL (γ x).val, (γ x).isUnit⟩ : invSet E a) := h.subtype_mk
  convert hu.measurable.comp hm using 1
  funext x
  ext1
  rfl

theorem measurable_of_mem_mspanR (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.mspanR π) : Measurable F := by
  have hF' := hF
  unfold GlobalTheory.JSW.mspanR at hF'
  refine Submodule.mem_sInf.1 hF' (measSub E a) ⟨fun φ hφ => ?_, fun F hF h => ?_,
    fun F hF X _ ν _ k γ hk => ?_⟩
  · exact (continuous_of_mem_or (π := π) (Or.inl hφ)).measurable
  · exact (hF : Measurable F).comp (continuous_mul_const h).measurable
  · have hγ : Measurable fun p : GA E a × X => p.1 * infGL E a (γ p.2) :=
      measurable_fst.mul ((GlobalTheory.ConstTermSmooth.continuous_infGL.measurable.comp
        (measurable_gl_of_matrix hk.2.1)).comp measurable_snd)
    have h1 : StronglyMeasurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) :=
      ((hk.1.comp measurable_snd).mul ((hF : Measurable F).comp hγ)).stronglyMeasurable
    exact (h1.integral_prod_right' (ν := ν)).measurable

theorem measurable_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Measurable fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  set s : Set (GA E a × (Fin a → Cinf E)) := Set.univ ×ˢ rowSet E ℓ with hsdef
  have hsm : MeasurableSet s := (isOpen_univ.prod (isOpen_rowSet ℓ)).measurableSet
  refine measurable_of_restrict_of_restrict_compl hsm ?_ ?_
  · have hc : Continuous fun p : s => p.1.1 * (infGL E a (rowGL ℓ p.1.2))⁻¹ := by
      have h2 : ContinuousOn (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) s :=
        continuous_fst.continuousOn.mul ((continuousOn_inv_rowGL ℓ).comp continuous_snd.continuousOn
          fun p hp => hp.2)
      exact h2.restrict
    have hm := hc.measurable
    exact ((h.comp hm).mul (Complex.continuous_conj.measurable.comp (h'.comp hm))).mul
      (hΦ.measurable.comp (measurable_snd.comp measurable_subtype_coe))
  · convert (measurable_const (a := (0 : ℂ)) : Measurable fun _ : (sᶜ : Set (GA E a × (Fin a → Cinf E))) => (0 : ℂ)) using 1
    funext p
    have hp : p.1.2 ∉ tsupport Φ := fun hp => p.2 ⟨trivial, hs hp⟩
    change rsInf ℓ φ φ' Φ p.1.1 p.1.2 = 0
    simp [rsInf, image_eq_zero_of_notMem_tsupport hp]

theorem measurable_rsPsi_vecMul {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (ξ : Fin a → E) :
    Measurable fun g : GA E a => rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := by
  have hY : Continuous fun g : GA E a => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val :=
    continuous_const.matrix_vecMul Units.continuous_val
  have hI : Continuous fun g : GA E a => fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i) :=
    continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp hY)
  have hF : Continuous fun g : GA E a => (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hY)).sub
      continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const
  exact ((measurable_rsInf h h' hΦ hs).comp (measurable_id.prodMk hI.measurable)).mul (h3.comp hF).measurable

theorem theta_integral_upper_mspan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (π π' : CuspSub E a), π.IsUnitary → π'.IsUnitary → ∀ φ φ' : Sm E a,
    (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') →
    ∀ Φ : (Fin a → Cinf E) → ℂ, Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ →
    (∀ g : GA E a, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} =>
      ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) ∧
    (∀ x : ℝ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (Differentiable ℂ fun s : ℂ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        (((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ) ∂μ := by
  intro E _ _ _ a ℓ π π' hπ hπ' φ φ' hφ hφ' Φ hΦ hc hs J η μ _ 𝓕 h𝓕
  have hdec : ∀ {ρ : CuspSub E a}, ρ.IsUnitary → ∀ {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Decays ψ.1 :=
    fun {ρ} hρ {ψ} hψ L hL C₀ hC₀ N => GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a ρ hρ ψ hψ [] L hL C₀ hC₀ N
  have hmeas : ∀ {ρ : CuspSub E a} {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Measurable ψ.1 :=
    fun {ρ} {ψ} hψ => hψ.elim (fun h => (continuous_of_mem_or (π := ρ) (Or.inl h)).measurable)
      (GlobalTheory.RSThetaM.measurable_of_mem_mspanR ρ)
  have hK := isSmallKernel_rsPsi (hdec hπ hφ) (hdec hπ' hφ') hΦ hc hs J η
  obtain ⟨C, hC⟩ := hK.tsum_le (N := 1) le_rfl
  obtain ⟨h1, h2, h3⟩ := hK.integrableOn μ h𝓕 fun ξ _ =>
    (GlobalTheory.RSThetaM.measurable_rsPsi_vecMul (hmeas hφ) (hmeas hφ') hΦ hs J η ξ).aestronglyMeasurable
  refine ⟨fun g => (hC g).1, h1, h2, h3, (h3.continuous.comp Complex.continuous_ofReal).congr fun x => ?_⟩
  refine integral_congr_ae (.of_forall fun g => ?_)
  exact congrArg _ (Complex.ofReal_cpow (ideleModule E _).2.le x).symm

end GlobalTheory.RSThetaM

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move



set_option maxRecDepth 100000 in
theorem heckeTie_of_same {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hsp : HEq D.sp D'.sp) {ρ : Setup X} {ρ' : Setup X'} {i : X.Tw} {i' : X'.Tw} (hi : HEq i i')
    {j : Fin D.R.m} {j' : Fin D'.R.m} (hj : (j : ℕ) = j') {b : Bool}
    (hmu : HEq (ρ.B i j b).mu (ρ'.B i' j' b).mu) (hlev : HEq (ρ.levK i j b) (ρ'.levK i' j' b))
    (r : Rd ρ Y i j b) (r' : Rd ρ' Y' i' j' b)
    (hR : ∀ (f : Y.Fm i ((j : ℕ) + 1) b) (f' : Y'.Fm i' ((j' : ℕ) + 1) b), HEq f f' → HEq (r' f') (r f))
    (ht : HeckeTie r) : HeckeTie r' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3 hsp
  subst a1; subst a2; subst a3; subst hsp
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hi
  obtain rfl : j = j' := Fin.ext hj
  have e : ∀ x, r' x = r x := fun x => eq_of_heq (hR x x HEq.rfl)
  have hmu' : (ρ'.B i j b).mu = (ρ.B i j b).mu := eq_of_heq hmu.symm
  have hlev' : ρ'.levK i j b = ρ.levK i j b := eq_of_heq hlev.symm
  have hk : ∀ k P R z F, ρ'.hecke i j b k P R z F = ρ.hecke i j b k P R z F := fun k P R z F => by
    funext x
    rw [Setup.hecke_apply, Setup.hecke_apply, hmu']
  have hd : ∀ k P α R z, ρ'.IsHeckeDatum i j b k P α R z ↔ ρ.IsHeckeDatum i j b k P α R z := fun k P α R z =>
    ⟨fun d => ⟨d.1, hlev' ▸ d.2, d.3⟩, fun d => ⟨d.1, hlev'.symm ▸ d.2, d.3⟩⟩
  have ha : ∀ k P f g, HeckeAt r' k P f g ↔ HeckeAt r k P f g := fun k P f g =>
    ⟨fun hg α R z d => by have := hg α R z ((hd k P α R z).2 d); rwa [e, e, hk] at this,
      fun hg α R z d => by rw [e, e, hk]; exact hg α R z ((hd k P α R z).1 d)⟩
  intro k P hkP f hf
  exact (ha k P f _).2 (ht k P hkP f (by obtain ⟨g, hg⟩ := hf; exact ⟨g, (ha k P f g).1 hg⟩))

theorem heckeTie_move_of_pin : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw},
    (∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) (b : Bool),
      HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b)) →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) := by
  intro D D' ι e h ρ ρ' hB rd rd' hr i i' hi j b ht
  have hR : ∀ (f : D.nexp.Fm i ((j : ℕ) + 1) b) (f' : D'.nexp.Fm i' ((h.cm j : ℕ) + 1) b), HEq f f' →
      HEq (rd' i' (h.cm j) b f') (rd i j b f) := fun f f' hf => by
    have h1 : h.fmCast hi ((j : ℕ) + 1) b f = f' := eq_of_heq ((h.fmCast_heq hi _ b f).trans hf)
    rw [← h1]
    exact hr i i' hi j b f
  exact heckeTie_of_same h.gal h.set h.frm h.sp hi (h.cm_val j).symm (hB i i' hi j b).1 (hB i i' hi j b).2
    (rd i j b) (rd' i' (h.cm j) b) hR ht



theorem SameData.mu_levK {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (hs : SameData ρ ρ') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i')
    (j : Fin D.R.m) (b : Bool) :
    HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b) := by
  have hj : (j : ℕ) = h.cm j := rfl
  generalize h.cm j = j' at hj
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  cases hi
  cases (Fin.ext hj : j = j')
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heckeTie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameData ρ ρ' →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) :=
  fun h _ _ hs => heckeTie_move_of_pin h (hs.mu_levK h)

end GlobalTheory.TwInputs.Move

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move.TieUp

theorem rds_eq {D : D7} {r : Rest D} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) {ρ : Setup D.ntw} {rd : Rds D.nexp ρ} {rd' : Rds (overD D r).nexp (setupUp r ρ)}
    (hr : RdRel h rd rd') : rd' = (rd) := by
  funext i j b
  refine LinearMap.ext fun f => ?_
  have h1 := hr ((i)) i ((HEq.refl i)) ((j)) b ((f))
  refine eq_of_heq ?_
  exact (h1)

theorem tie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameSetup ρ ρ' → ∀ (hρ : ρ.Good) (hρ' : ρ'.Good)
    (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ T : Comparison₂ hρ rd,
    ∃ T' : Comparison₂ hρ' rd', ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
      HEq (T i j b).rdV (T' i' (h.cm j) b).rdV := by
  intro D D' ι e h ρ ρ' hs hρ hρ' rd rd' hr T
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  have hrd := rds_eq h hr
  subst hrd
  refine ⟨fun i j b => (cellUp r h hρ' (T i j b)), fun i i' hi j b => ?_⟩
  cases hi
  exact (cellUp_rdV r h hρ' (T i j b))

end GlobalTheory.TwInputs.Move.TieUp

end
end
