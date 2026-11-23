module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.ChainTwOk
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.Bundle024
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.Bundle033
public import Formalism.LocalToGlobal.Columns.Bundle027
public import Formalism.LocalToGlobal.Columns.Bundle036
public import Formalism.LocalToGlobal.Columns.Bundle043
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

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerStd

def SeriesRatS : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → VStd D i →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
        SeriesRatOn T R i hV C (κ i) u (c0L i) ph

def UntwRatS : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → VStd D i →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
        ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
          IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
          ∀ w ∈ ratVec R i (c0L i) C.σ₂.fieldRange,
            IsRat T i hV C (κ i) (fun g => ph * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f))

theorem seriesRatS_of (h : SeriesRat) : SeriesRatS := by
  first
    | exact h
    | exact fun D G _ _ Pl0 T0 A T _ R F κ v₀ a b c d e f g i hV hp _ => h D G Pl0 T0 A T R F κ v₀ a b c d e f g i hV hp

end GlobalTheory.SerStd
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cx_zs_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) (κ lam e) : (reErr (reScal Y κ lam) e).zs = Y.zs := rfl

theorem cx_liftMat_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) : (reErr (reScal Y κ lam) e).liftMat cr b j t = Y.liftMat cr b j t := by
  have h : (reErr (reScal Y κ lam) e).liftMatC cr b j t = Y.liftMatC cr b j t := by
    unfold CxData.liftMatC
    rfl
  exact congrArg (kMat Bs.v0.embedding) h

theorem cx_Iw_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) :
    ((reErr (reScal Y κ lam) e).data cr b).Iw j t w = (Y.data cr b).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M b j) (Formalism.DivisionValues.matLat M ((lv (fc Y.zs) b).Tl j t))) (cx_liftMat_scal Y cr κ lam e b j t)

theorem definiteComplexNonzeroIndexPlaces_rescale_errors {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : (reErr (reScal Y κ lam) e).W1 cr N w ↔ Y.W1 cr N w :=
  exists_congr fun j => or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _)))
    (or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _))) Iff.rfl)

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} (Y : CxData A3.fam3.amb3) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
  (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc Dc' : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
  (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Sp' : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc' Zs))
  (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem cx_tC_face (j : Fin m) (t : T) :
    Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t := rfl

theorem cx_liftMat_face (j : Fin m) (t : T) :
    Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t :=
  congrArg (fun g => kMat A3.fam3.base3.v0.embedding (relMat (Y.w0C false j) g)) (cx_tC_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem cx_Iw_face (j : Fin m) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false).Iw j t w = (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M false j) (Formalism.DivisionValues.matLat M ((A3.side3 P0 ψ0 Y.zs).Tl j t)))
    (cx_liftMat_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem definiteSide_nonzeroIndexPlaces_any_columns_scale (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 K)) :
    Y.W1 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') N w ↔ ∃ j : Fin m,
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 w ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) w ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨ N.F0 w j ≠ 0) ∨
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 (Formalism.DivisionValues.conjPl w) ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) (Formalism.DivisionValues.conjPl w) ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨
          N.F0 (Formalism.DivisionValues.conjPl w) j ≠ 0) := by
  refine exists_congr fun j => ?_
  rw [← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j, ← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j]
  have key : ∀ a b c d e f : Prop, (a ∨ b ∨ c ∨ d ∨ e ∨ f) ↔ (a ∨ c ∨ e) ∨ (b ∨ d ∨ f) := fun _ _ _ _ _ _ => by tauto
  exact key _ _ _ _ _ _

end Cx

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def NzAt (R : RealDat3 D A3 Ks) (F : Face3 D A3) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (s0Of R F).Iw j A3.A.μ0 w ≠ 0 ∨
    Formalism.DivisionValues.jw ((A3.side3 F.P0 F.ψ0 (zsOf R F)).HT j A3.A.μ0) w ((A3.side3 F.P0 F.ψ0 (zsOf R F)).Tl j A3.A.μ0) ≠ 0 ∨ F0 w j ≠ 0



theorem toCx3_upd_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc) = reErr (reScal (R.toCx3 F) (fun _ => kap) lam) err := rfl



theorem complexSide_nonzeroIndexPlaces_iff (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (N : IndefNum A3.fam3.base3)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).W1 (reFace F Dc Sp Zsc).cr N w ↔
      ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  rw [e]
  exact (definiteComplexNonzeroIndexPlaces_rescale_errors (R.toCx3 F) _ _ _ _ N w).trans (definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc Dc F.Sp Sp F.Zsc Zsc N w)



theorem complexSide_nonzeroIndexPlaces_iff_self (R : RealDat3 D A3 Ks) (F : Face3 D A3) (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (R.toCx3 F).W1 F.cr N w ↔ ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) :=
  definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Dc F.Sp F.Sp F.Zsc F.Zsc N w



theorem nzAt_res {f : T' → T} {μ : T'} (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    NzAt (Res.dat3 f μ R mu tw) (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w ↔ NzAt R (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w := Iff.rfl



theorem complexSide_numberContents_eq_scaleAtSubspaces (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (C CH : ℝ) :
    (((R.updS kap lam).withErr err).num (reFace F Dc Sp Zsc) C CH).F0 = (Zsc (zsOf R F)).F0 := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  have e2 : (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).zs = (R.toCx3 F).zs :=
    (congrArg CxData.zs e).trans (cx_zs_scal (R.toCx3 F) _ _ _)
  have e3 : ∀ (F' : Face3 D A3) (s : DefSub A3.fam3.amb3), ((F'.fc s).Z.num C CH).F0 = (F'.Zsc s).F0 := fun _ _ => rfl
  exact (e3 (reFace F Dc Sp Zsc) _).trans (congrArg (fun s => (Zsc s).F0) e2)

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem _root_.GlobalTheory.Mem.R3.columnChoiceReferenceFace_eq_bareFaceTwoLevels (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) :
    face0 X I hX U Xg tr = Res.bare3 (famR X I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) := rfl



def resGeo (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.GeoHalf z.core (z.resR h).toRealDat fun _ => 1 :=
  Res.geoHalf (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') z.geo





theorem levOf_resR (h : Wt' ⊆ Wt) : LevOf X I (usedOf I T Wt') (z.resR h).toLevCh :=
  ⟨Res.levCh_is (L := z.R.toLevCh) (inclU_injective (usedOf_mono I T h)) z.lev.is,
    z.lev.C,
    fun t => z.lev.xiH (inclU I (usedOf_mono I T h) t),
    z.lev.Pg,
    fun t => z.lev.Q (inclU I (usedOf_mono I T h) t),
    z.lev.beta⟩

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def IsTw : Prop := ∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧
  I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)

@[reducible] def canon : TC B X :=
  { I with
    cst := fun a => twCst I.Ch I.sel (I.tup a) I.glob
    idx := fun a => twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) }

theorem canon_isTw : I.canon.IsTw := fun _ => ⟨rfl, rfl⟩

def Deep : Prop := ∀ a (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∉ (B.primes X).vGs → 2 * B.R.m ≤ (I.cst a).D P

variable {I}

theorem IsTw.cst_eq (h : I.IsTw) (a : I.ι) : I.cst a = twCst I.Ch I.sel (I.tup a) I.glob := (h a).1

theorem IsTw.idx_eq (h : I.IsTw) (a : I.ι) :
    I.idx a = twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) := by
  rw [(h a).2, (h a).1]

theorem IsTw.deep (h : I.IsTw) : I.Deep := fun a P hP => by
  rw [h.cst_eq a, twCst_D_Q hP]

theorem qOf_mod_four (B : Base) (X : PreX B.toPre) : ∀ w ∈ (B.primes X).vGs, qOf w % 4 = 1 := fun w hw => by
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨k, hk⟩ : ∃ k, w ∈ (B.primes X).vG k := by
    classical
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  rw [show qOf w = (B.primes X).g k from hPr.vG_norm k w hk]
  exact (hPr.g_cong k).of_dvd (by
    show 4 ∣ B.host.QS * B.host.q * B.host.d
    exact (((pow_dvd_pow 2 (Nat.le_add_left 2 B.R.e) : 2 ^ 2 ∣ 2 ^ (B.R.e + 2)).trans B.host.tower_dvd).mul_right _).mul_right _)

theorem val_of_ok (h : I.Ok) (j : Fin B.R.m) (w : HeightOneSpectrum (𝓞 B.fields.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ y : B.fields.K, I.glob.σ₀ y = ((((I.glob.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hq : (qOf w : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  have e := (h.idx_ok I.mu0).muqG j j.2 ⟨w, Finset.mem_union_left _ hw⟩ hw (ciQU w) (by simp [ciQU, hq])
  refine ⟨(I.cst I.mu0).muq (j + 1) ⟨w, Finset.mem_union_left _ hw⟩ *
    (qValC (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) w : B.fields.Kˣ), ?_⟩
  rw [map_mul, e, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

theorem Q_notMem_of_ok (h : I.Ok) (a : I.ι) : ∀ P ∈ I.Q a, P ∉ (B.primes X).vGs := fun _ hP =>
  IdxEx.notMem_vGs_of_mem_QE (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok h.g_mem (I.tup a) hP

theorem degOne_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : TwDegOne B.fields P.1 :=
  degOneUnram_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok (I.tup a) P

theorem sqrt_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : ∃ z : B.fields.K, z ^ 2 = (qOf P.1 : B.fields.K) :=
  ⟨_, (h.idx_ok a).cst_ok.sq_sq P⟩

theorem root_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs) :
    ∃ z : B.fields.K, I.glob.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * B.R.m) : ℕ) : ℂ)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hD a P hP)
  have hq : (qOf P.1 : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hqC : (qOf P.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  obtain ⟨x1, x2⟩ := (h.idx_ok a).xiUnitAtPrime P
  have hx : I.glob.xi0 ≠ 0 := fun e => x2 (e ▸ redP_zero)
  have hi : IntAt P.1 ((qOf P.1 ^ k : ℕ) : B.fields.E) := by
    simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 ((qOf P.1 ^ k : ℕ) : ℤ)
  have e := (h.idx_ok a).weil P (I.glob.xi0⁻¹ / (qOf P.1 : B.fields.E) ^ (2 * B.R.m)) ((qOf P.1 ^ k : ℕ) : ℤ)
    (by
      convert hi.mul (yIntAt_inv x1 x2) using 1
      rw [hk]; push_cast; field_simp; ring)
    (by
      convert GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 0 using 1
      rw [hk]; push_cast; field_simp; ring)
  refine ⟨_, e.trans ?_⟩
  congr 1
  rw [hk]; push_cast; field_simp; ring

theorem twIdx_ok_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) :
    (twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2)).Ok I.Ch I.sel (I.tup a)
      (twCst I.Ch I.sel (I.tup a) I.glob) I.glob (B.R.m - 2) :=
  twIdx_ok_closed (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.ch_ok (qOf_mod_four B X) I.glob
    h.ch_tied h.weil (val_of_ok h) h.hm (Q_notMem_of_ok h a) (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a)
    (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)

theorem canon_ok (h : I.Ok) (hD : I.Deep) : I.canon.Ok :=
  { h with sharp := fun _ => rfl, idx_ok := twIdx_ok_of_ok (I := I) h hD }

theorem IsTw.chF_ok (ht : I.IsTw) (h : I.Ok) (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : (B.primes X).Word) (j : ℕ) :
    (chF W I.sel (I.tup a) (I.idx a) u j).Ok := by
  have ho : ∀ b, ThetaOpen ((I.idx a).levQ j b) := by
    rw [(ht a).2]
    exact thetaOpen_twIdx I.Ch I.sel (I.tup a) (I.cst a) (h.idx_ok a).cst_ok (Q_notMem_of_ok h a) _ j
  exact chF_ok_of_finIdx W I.sel (I.tup a) _ (base_fields_primes_ok B X).1 u j
    (fun b P => thetaOpen_finIdx _ (ho b) P) (fun b c => thetaOpen_root _ (ho b) c)

end GlobalTheory.Mem.Col2.TC

end
end
