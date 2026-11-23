module

public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idealLatHat (V : HSp D) (I : Ideal (𝓞 D.host.E)) :
    AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ b ∈ I, ∃ z ∈ latGHat V 1, w = halfVec V b z}

def IsLift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (g : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) (k : GA D V) : Prop :=
  k ∈ GfC V ∧ gLat V k = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
    ∀ a b : Dw.La, (Submodule.Quotient.mk b : LaMod Dw l) = g (Submodule.Quotient.mk a) →
      (finHom V k).1.mulVec (finVec V (ι a)) - finVec V (ι b) ∈ idealLatHat V l.Mb

abbrev LevGrp (T : CoreJ D) (j : ℕ) : Type :=
  LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def iotaAt (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (hr : (T.V j σ).rank = D.R.r) :
    (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (T.V j σ).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

attribute [local instance 2000] Submodule.module

def IsGeoRep (T : CoreJ D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)) : Prop :=
  ∀ g f, ((ρ g f : T.cuspA j a n) : T.R j) =
    actLev (Xo := T.Q.Xo j) T.Q.c (GlobalTheory.FormTies.levFull (T.Q.Dw j) T.Q.l) g (f : T.R j)

def IsChiDet (T : CoreJ D) (j : ℕ) {V : HSp D} (ℓ : LevGrp T j → GA D V) (chi : LevGrp T j →* T.Q.c.Fˣ) : Prop :=
  ∀ g x, FinUnit x → IsDetRoot V (ℓ g) x →
    T.σ₀ ((chi g : T.Q.c.Fˣ) : T.Q.c.F) * ((T.chiW j T.σ₀ x : Circle) : ℂ) = 1

def UnitConstEquivariant : Prop :=
  ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)), IsGeoRep T j a n ρ →
    ∀ (chi : LevGrp T j →* T.Q.c.Fˣ) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    ∀ (hr : (T.V j σ).rank = D.R.r) (ℓ : LevGrp T j → GA D (T.V j σ)),
      (∀ g, IsLift (T.V j σ) (T.Q.Dw j) T.Q.l (iotaAt T j σ hr) g (ℓ g)) → IsChiDet T j ℓ chi →
      ∃ c' : (T.U j σ).Comp → ℂ, CUnit c' ∧
        EquivariantFiniteGroup (T.V j σ) σ ((rdU (T.U j σ)).comp (T.cuspA j a n).subtype) (T.dict j σ)
          (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) c') ρ chi ℓ

end GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

variable {D : D7}

section Local


variable (D) in
abbrev Oh : Subring (Datum.EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def InI (I : Ideal (𝓞 D.host.E)) (z : Datum.EAf D) : Prop := ∃ h : z ∈ Oh D, (⟨z, h⟩ : Oh D) ∈ idS D.host.F I

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

variable {a a' d₁ d₂ : ℕ}

variable (hd : a + a' = d₁ + d₂) (h : GL (Fin (d₁ + d₂)) (AE D))

end Local

section Models

variable (ψ : AddChar (AF D.host.F) ℂ)


open Classical in
def IsDatOwn (ε : Bool) (S T : Node D) (e : AE D) (f₀ : WO S.V T.V → ℂ)
    (φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ) (f : WO S.V T.V → ℂ) : Prop :=
  IsSBHalf e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True)
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) ∧
    IsThetaAt ψ (symplO (sgn ε S.V) T.V) (heisO ψ (sgn ε S.V) T.V) e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True) 1 f₀
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) f


end Models

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)





end Grid

section Basic₂

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridDat R}

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev Cusp : Type := T.cuspA ((i : ℕ) + 1) (wtA w) w.n

local instance cuspModule : Module T.Q.c.F (Cusp T i w) :=
  (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).module

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

def iotaW : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def IsLift (g : G) (κ : GA D (Wc D i)) : Prop :=
  Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ



def IsGeo (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∃ lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) lev ∧
    ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) ∧
    ∀ g (f : Cusp T i w), ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) =
      actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) g (f : T.R ((i : ℕ) + 1))

def ReadTwist (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ (g : G) (κ : GA D (T.V ((i : ℕ) + 1) (res T σ))), IsLift T R i g (cast (congrArg (GA D) hV) κ) →
      ∀ (f : Cusp T i w) (x : GA D (T.V ((i : ℕ) + 1) (res T σ))),
        T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) x =
          σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) *
            T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) (f : T.R ((i : ℕ) + 1)) (x * κ)

def IsIntegralForm (f : Cusp T i w) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM ((i : ℕ) + 1) la),
    T.nrmM ((i : ℕ) + 1) la y (f : T.R ((i : ℕ) + 1)) ≤ 1

def KeepsIntegral (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ g f, IsIntegralForm T i w f → IsIntegralForm T i w (ρ g f)

def ConstEquiv : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ →
    ∀ chi : G →* (T.Q.c.F)ˣ,
      (∀ g, algebraMap T.Q.c.F D.what₂.LL (chi g : T.Q.c.F) = (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) →
    ∀ ℓ : G → GA D (T.V ((i : ℕ) + 1) (res T σ)), (∀ g, IsLift T R i g (cast (congrArg (GA D) hV) (ℓ g))) →
      CEquiv (T.V ((i : ℕ) + 1) (res T σ)) (res T σ)
        ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).subtype)
        (T.dict ((i : ℕ) + 1) (res T σ)) (T.mu ((i : ℕ) + 1) (res T σ)) (T.cE ((i : ℕ) + 1) (res T σ)) ρ chi ℓ


omit [Algebra T.Q.c.F D.what₂.LL] in
def IsKappa : Prop :=
  ∀ τ : D.what₂.Tau,
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ w.n = D.R.nV

def GeoActAt : Prop :=
  ∃ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ ∧ ReadTwist T R i w ρ ∧ KeepsIntegral T i w ρ

end GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv
end
end
