module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle012
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle024
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
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

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure CxPassIn3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (C CH : ℝ)
    (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : Prop where

  ratMuP : X.RATmu (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false

  isGood : Formalism.IndefR.TransferLatticeStatement.IsGood τ

  chars : Formalism.IndefR.CxPass.CharsX τ A3.A.fam.X

  m1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩

  nbarPos : 0 < nbar

  near_constant_multiplicities : Formalism.IndefR.CxPass.NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de

  laTie : ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G

section Pass3

variable [_root_.NumberField.IsTotallyComplex K] {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {X : CxData A3.fam3.amb3} {s : ℕ} {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH} {C CH : ℝ}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)} {cf : ConvFace A3.fam3.base3}
  {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
  [∀ s, FiniteDimensional K (Ws s)] {τ : ∀ s, Representation K G (Ws s)} {nbar : ℝ}

theorem passage3_of (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true) :=
  Formalism.IndefR.CxPass.cutPassage3S K G Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S Ws τ nbar hN.ok hN.sep
    hN.stable hN.inBlock hN.h4pos (hN.pos false) (hN.pos true) (fun b => (hN.what₂ b).1) hN.ratMu hN.h2P hP.ratMuP
    hN.gUnit hN.gEquiv hN.npTie.1 hN.npTie.2 hP.isGood hP.chars hP.m1 hP.nbarPos hP.near_constant_multiplicities hP.laTie

def packageFullHecke (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH :=
  basePackageFullHecke { toPrimitiveStatementsBaseLiftsOnly := hN, passage := passage3_of hN hP }

end Pass3

end Formalism.IndefR.Cx
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
structure FWTie (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) where

  alg_eq : ∀ x : 𝓞 T.Q.c.F, algebraMap T.Q.c.F D.what₂.LL (x : T.Q.c.F) = D.what₂.OtoLL (T.Q.eO x)

  e : ∀ i : Fin D.R.m, T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n ≃ₗ[T.Q.c.F] (R.FW i).WK

  ks : ∀ i : Fin D.R.m, (R.FW i).IsKsForm

  kap : ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, (κ i).aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      (κ i).aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ (κ i).n = D.R.nV

  pt : ∀ (i : Fin D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (R.FW i).Pt la ≃ T.PtM ((i : ℕ) + 1) la

  nrm_eq : ∀ (i : Fin D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : (R.FW i).Pt la) (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n),
    (R.FW i).nrm la y (e i f) = T.nrmM ((i : ℕ) + 1) la (pt i la y) (f : T.R ((i : ℕ) + 1))

  laws : LawsJ T

  chiR : ChiR T R

  hv₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsChosenExtremalVector R i σ (v₀ i σ)

  x0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)))

  ev0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∀ hV : T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) = Wc D i,
    (¬ ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H, ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e (j' ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) →
    (R.FW i).j σ = 0

  ev : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∀ hV : T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) = Wc D i,
    (∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H, ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e (j' ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) →
    ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e ((R.FW i).j σ ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))

end Formalism.IndefR.FWT
end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace
open IsDedekindDomain NumberField MeasureTheory

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FromLinks

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure PartsRec (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) {n : ℕ}
    (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n)
    (eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0))
    {Xd : DivX D} (E : EigIdx D Xd) (labPi : E.Pi → A.fam.base.Ix)
    (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (prtE : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0)))
    (prtWf : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A)))) : Prop where

  cOf : ∀ π, piOf (E.cOf π) = principalLevelFrame.cOfT (PW ⟨0, hm⟩)
    (levS _ (R.βW ⟨0, hm⟩) (R.datWp ⟨0, hm⟩ (R.levL F false (sg0 D A))))
    (levChi _ (R.βW ⟨0, hm⟩) (R.datWp ⟨0, hm⟩ (R.levL F false (sg0 D A)))) (SsetF R (tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (eFT π))

  piOf_inj : Function.Injective piOf

  prt : ∀ π, prtE π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q
    (RealDat.polE (A := A) (labPi (E.cOf π)).1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtW : ∀ i π, prtWf i π ≤ (hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q
    (RealDat.polW (A := A) (labPi (E.cOf π)).1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap

end FromLinks

end Formalism.IndefR.RecTie

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FromLinks

open Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MtRead (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (IL : LiftIds (toLiftReal R F tupT hm hTop hinj))
    (tw : ∀ μ (i : Fin D.R.m), D.what₂.MtL μ (i + 1) → A.fam.amb.FL i (tupT μ)) : Prop :=
  ∀ μ (hμ : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.MtL μ (i + 1)),
    (IL.jMt μ hμ i (D.what₂.jMt μ (i + 1) x)).1 = R.extV i (tupT μ) (R.jV i (tupT μ) (tw μ i x))

def ThetaFireL {D : D7} {C : ChainReal D} (L : LiftReal D C) (I : LiftIds L) : Prop :=
  ∀ μ (hμ : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i + 1)), ∃ w : L.AmbW i,
    w ∈ L.MultW i ∧ w ∘ₗ L.embK i = L.thC μ i (I.jMt μ hμ i x) ∧ L.eW i ∘ₗ w ∈ L.Wc i

def ResInjL {D : D7} {C : ChainReal D} (L : LiftReal D C) : Prop :=
  ∀ (i : Fin D.R.m) (w : L.AmbW i), w ∈ L.MultW i → w ∘ₗ L.embK i = 0 → w = 0

def ThetaFireRow {D : D7} {C : ChainReal D} (L : LiftReal D C) (I : LiftIds L) : Prop :=
  (∀ μ, Used0 D μ → ∀ i, Lift.IsThetaP (L.measV μ i) (L.fdV μ i) (L.thW μ i) (L.ptW μ i) (L.ioK i) (L.Amt μ i)
    (L.thC μ i)) ∧ ThetaFireL L I ∧ ResInjL L

def MjRead (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (IL : LiftIds (toLiftReal R F tupT hm hTop hinj))
    (nj : Fin D.R.m → ℕ) (crd : ∀ i : Fin D.R.m, (Fin (nj i) → D.what₂.LL) → D.what₂.Mj (i + 1))
    (jD : ∀ i : Fin D.R.m, (Fin (nj i) → D.what₂.LL) → (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∀ (i : Fin D.R.m) (y : Fin (nj i) → D.what₂.LL),
    ((IL.jMj i (crd i y) : (toLiftReal R F tupT hm hTop hinj).Wc i) : (toLiftReal R F tupT hm hTop hinj).AmbW i) =
      PiTensorProduct.lift (Mult.postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A))
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (jD i y))))

end FromLinks

end Formalism.IndefR.RecTie

end
end

section

noncomputable section

open NumberField
open scoped TensorProduct

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev inC {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c' : Coeff l) : c'.F →+* ℂ := c'.F.val.toRingHom

abbrev sOv (C : Core D) (c' : Coeff C.Q.l) (hle : C.Q.c.F ≤ c'.F) : C.Q.c.F →+* ℂ := (inC c').comp (incF C.Q.c c' hle)

theorem sOv_eq (C : Core D) (c' : Coeff C.Q.l) (hle : C.Q.c.F ≤ c'.F) : sOv C c' hle = C.σ₀ := by
  first
  | rfl
  | (ext x; rfl)
  | (ext x; simp [sOv, inC, incF])


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure OMDat (C : Core D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) : Type 1 where
  c' : Coeff C.Q.l
  hle : C.Q.c.F ≤ c'.F
  jL : D.what₂.LL →+* c'.F
  hV : C.V ((i : ℕ) + 1) (sOv C c' hle) = Wc D i
  c0' : VsV D i c'.F →ₛₗ[inC c'] (R.cV i).W
  lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La
  dδ : Tp → DeltaDat (C.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank
  Cl' : Tp → Type
  [fCl : ∀ t, Fintype (Cl' t)]
  bad : Tp → ℕ
  Lh : ∀ t, Cl' t → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)
  La : ∀ t, Cl' t → GenLat D.host.E (Vc D i).rank
  Nc : ∀ t, Cl' t → ℕ
  gam : ∀ t, Cl' t → ℕ
  vol : Tp → c'.F
  ep : ∀ t, Cl' t → c'.F
  B : Tp → Ideal (𝓞 D.host.E) → c'.F
  epF : Tp → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F
  io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F
  hw : VsV D i c'.F
  φ : ∀ t, (Fin (Vc D i).rank → LevQc (C.Q.Dw ((i : ℕ) + 1)) (dδ t).l₂) → c'.F
  w : ∀ t, Cl' t → (Fin (Vc D i).rank → LevQ (C.Q.Dw ((i : ℕ) + 1)) (dδ t).l₂) → c'.F
  U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((inC c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) D.R.r
  dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r
  xi : Tp → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  thAd : ∀ t, (Cl' t → VsV D i c'.F) → AutQ (Wc D i) → ℂ
  Plc : ∀ t, (Cl' t → VsV D i c'.F) → Prop

attribute [instance] OMDat.fCl

namespace OMDat

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup)

abbrev s0 : C.Q.c.F →+* ℂ := sOv C O.c' O.hle

abbrev lev2 (g : G) := (O.lev g, (LinearMap.id : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La))

abbrev dict := castDict O.hV (C.dict ((i : ℕ) + 1) O.s0)

abbrev mu : GA D (Wc D i) → ℂ := castDict O.hV (C.mu ((i : ℕ) + 1) O.s0)

def phi (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) O.dict (muPin (Wc D i) O.dict O.mu cc) (rdU (C.U ((i : ℕ) + 1) O.s0) f)

variable (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def EquivAt (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
    ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, actLev C.Q.c O.lev2 g f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n ∧ ∀ h,
      O.phi cc (actLev C.Q.c O.lev2 g f) h =
        (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)) * O.phi cc f (h * k)

def PhRat (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  ∀ x : A.fam.amb.FL i A.μ0, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
    ph * (R.HW i (sg0 D A)).e (R.thG i A.μ0 (jVx R i A.μ0 x)) v₀ h =
      ∑ k, D.what₂.embLL (a k) * ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)

structure Pins (v₀ : (R.MW i (sg0 D A)).Vec)
    (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop where
  lift : ThPinsR R i O.jL (inC O.c') v₀ O.c0' ι C.Q.l.M (Mfr C.Q.l) O.lev
  tuple : ∀ t, ThPinsT R i (inC O.c') (tup t) v₀ O.c0' ι (O.bad t) C.Q.l.Mb (O.dδ t).I (Mfr (O.dδ t).l₂ • ⊤) (O.Lh t) (O.gam t)
    (O.vol t) (O.B t) (O.xi t) (O.φ t) (O.thAd t) (O.Plc t)
  act : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2 ∧ ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2
  bad : ∀ t, 0 < O.bad t ∧ BadPin (O.bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1)
  reps : RepsCov (C.Q.Xo ((i : ℕ) + 1)) O.c' O.Cl' O.dδ O.bad O.Lh O.La O.Nc O.gam
  ep : ∀ t, (∀ k, O.ep t k = O.epF t (O.Lh t k)) ∧ EpIs (Dw := C.Q.Dw ((i : ℕ) + 1)) O.c' (O.bad t) (O.B t) (O.epF t)
  io : IoLFRec O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (wtA κ) O.io O.hw
  w : WPin (C.Q.Xo ((i : ℕ) + 1)) O.c' O.Cl' O.dδ O.φ O.w
  cov : CovPin (C.Q.Xo ((i : ℕ) + 1)) O.c' O.dδ
  cxi : CXiVal (Wc D i) (rank_Wc i) (inC O.c') O.dδ O.U₂ O.dict₂ ι x₀ O.xi
  model₂ : ∀ t k, ModelW (Wc D i) (rank_Wc i) ((O.U₂ t).X k)

def OneMapOf (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  O.EquivAt κ cc ∧
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (C.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA κ)
      (actLev C.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc ph ∧
    O.PhRat κ v₀ cc ph

end OMDat

def QHalf {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ t, ∀ PP ∈ R.Q t, ∀ PP' ∈ R.Q t, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def QGuard {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  QHalf R ∧ ∀ t, ∀ PP ∈ R.Q t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

def iotaW (i : Fin D.R.m) : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def OMPins (i : Fin D.R.m) : Prop :=
  (O i).c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧ (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (O i).s0)

def OneMapRow0 (i : Fin D.R.m) : Prop := ∃ cc ph, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph

def PhaseTie (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i → (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) (ph i)

def OneMapRowR (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i ∧
    (QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
      O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧
        O'.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O'.s0) (ph i))

theorem phi_cE (i : Fin D.R.m) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) f h =
      ((O i).hV ▸ T.phiJ ((i : ℕ) + 1) (O i).s0 a f : GA D (Wc D i) → ℂ) h := by
  have key : ∀ (σ : T.Q.c.F →+* ℂ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W),
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f) g = (hV ▸ T.phiJ ((i : ℕ) + 1) σ a f : GA D W → ℂ) g := by
    intro σ W hV g
    subst hV
    rfl
  exact key _ _ (O i).hV h

end Comparison₂

end Formalism.IndefR.FWT
end
end
