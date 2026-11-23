module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle482
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnChoice_cloudBound_le_cG : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧ ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L := by
  first | exact @GlobalTheory.Mem.Top.Bl.cloudBound_step | exact GlobalTheory.Mem.Top.Bl.cloudBound_step | (intros; apply GlobalTheory.Mem.Top.Bl.cloudBound_step <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl

theorem exists_below_between : ∀ (D₁ D₂ D₃ : Formalism.BasicNotions.D7), Set.range D₂.what₂.embLL ⊆ Set.range D₃.what₂.embLL → ∀ (v₁ : D₁.what₂.places.Pl) (v₃ : D₃.what₂.places.Pl), GlobalTheory.Mem.Top.Bl.Below D₁ D₃ v₁ v₃ → ∃ v₂ : D₂.what₂.places.Pl, GlobalTheory.Mem.Top.Bl.Below D₁ D₂ v₁ v₂ ∧ GlobalTheory.Mem.Top.Bl.Below D₂ D₃ v₂ v₃ := by
  intro D₁ D₂ D₃ hR v₁ v₃ h13

  have hmem : ∀ x : D₂.what₂.LL, D₂.what₂.embLL x ∈ D₃.what₂.embLL.fieldRange := fun x => by
    obtain ⟨y, hy⟩ := hR ⟨x, rfl⟩
    exact ⟨y, hy⟩
  let ι : D₂.what₂.LL →+* D₃.what₂.LL :=
    (D₃.what₂.embLL.rangeRestrictFieldEquiv).symm.toRingHom.comp (D₂.what₂.embLL.codRestrict _ hmem)
  have hι : ∀ x, D₃.what₂.embLL (ι x) = D₂.what₂.embLL x := fun x => by
    have := (D₃.what₂.embLL.rangeRestrictFieldEquiv).apply_symm_apply ⟨D₂.what₂.embLL x, hmem x⟩
    exact congrArg Subtype.val this
  let ιO : 𝓞 D₂.what₂.LL →+* 𝓞 D₃.what₂.LL := RingOfIntegers.mapRingHom ι
  have hιO : ∀ x : 𝓞 D₂.what₂.LL, ((ιO x : 𝓞 D₃.what₂.LL) : D₃.what₂.LL) = ι (x : D₂.what₂.LL) := fun x => rfl
  set Q := (D₃.plEq v₃).asIdeal with hQ
  let P : Ideal (𝓞 D₂.what₂.LL) := Q.comap ιO
  have hPprime : P.IsPrime := Ideal.comap_isPrime ιO Q
  have hQne : Q ≠ ⊥ := (D₃.plEq v₃).ne_bot
  have hn : Ideal.absNorm Q ≠ 0 := by
    intro h; exact hQne (Ideal.absNorm_eq_zero_iff.mp h)
  have hPne : P ≠ ⊥ := by
    intro h
    have hin : ((Ideal.absNorm Q : ℕ) : 𝓞 D₂.what₂.LL) ∈ P := by
      show ιO _ ∈ Q
      rw [map_natCast]; exact Ideal.absNorm_mem Q
    rw [h, Ideal.mem_bot] at hin
    exact hn (by exact_mod_cast hin)
  refine ⟨D₂.plEq.symm ⟨P, hPprime, hPne⟩, ?_, ?_⟩
  · intro x₁ x₂ hx
    rw [Equiv.apply_symm_apply]
    show x₁ ∈ (D₁.plEq v₁).asIdeal ↔ ιO x₂ ∈ Q
    exact h13 x₁ (ιO x₂) (by rw [hιO, hι]; exact hx)
  · intro x₂ x₃ hx
    rw [Equiv.apply_symm_apply]
    show ιO x₂ ∈ Q ↔ x₃ ∈ Q
    have : ιO x₂ = x₃ := by
      apply Subtype.ext
      apply D₃.what₂.embLL.injective
      show D₃.what₂.embLL (ι (x₂ : D₂.what₂.LL)) = _
      rw [hι]; exact hx
    rw [this]

end GlobalTheory.Mem.Top.Bl
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.Mem.Top.Bl.ThTTr

open Formalism.L2.Theta Formalism.L2.JoinChr
open scoped TensorProduct
open Formalism.BasicNotions.TH (tauE)

section

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt)
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

abbrev thTrZ (X : ThetaX (w.D Z)) : ThetaX (w.D (setDivZ Z N h)) := { X with }

theorem isAutFun_tr {V : TH.HSp (w.D Z)} {φ : GA (w.D Z) V → ℂ} :
    IsAutFun (D := w.D Z) V φ ↔ IsAutFun (D := w.D (setDivZ Z N h)) V φ :=
  ⟨fun x => ⟨x.left, x.level, x.cont⟩, fun x => ⟨x.left, x.level, x.cont⟩⟩

theorem isAutFunSm_tr {θ : (w.D Z).what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf (w.D Z).host.F ⊗[(w.D Z).host.F] (w.D Z).host.E →+* ℂ)} {V : TH.HSp (w.D Z)}
    {φ : GA (w.D Z) V → ℂ} : IsAutFunSm (D := w.D Z) θ V φ ↔ IsAutFunSm (D := w.D (setDivZ Z N h)) θ V φ :=
  ⟨fun x => ⟨(isAutFun_tr w Z N h).1 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩,
   fun x => ⟨(isAutFun_tr w Z N h).2 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩⟩

theorem isThetaFun_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF (w.D Z).host.F) ℂ} {V W : TH.HSp (w.D Z)} {f : WA V W → ℂ} :
    IsThetaFun (D := w.D Z) ψ V W f ↔ IsThetaFun (D := w.D (setDivZ Z N h)) ψ V W f :=
  ⟨fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩, fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩⟩

theorem isPolFock_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF (w.D Z).host.F) ℂ}
    {θ : (w.D Z).what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf (w.D Z).host.F ⊗[(w.D Z).host.F] (w.D Z).host.E →+* ℂ)} {V W : TH.HSp (w.D Z)}
    {A : ∀ τ : (w.D Z).what₂.Tau, Matrix (Fin (V.sig (tauE (w.D Z) τ)).1 ⊕ Fin (V.sig (tauE (w.D Z) τ)).2) (Fin V.rank) ℂ}
    {B : ∀ τ : (w.D Z).what₂.Tau, Matrix (Fin (W.sig (tauE (w.D Z) τ)).1 ⊕ Fin (W.sig (tauE (w.D Z) τ)).2) (Fin W.rank) ℂ}
    {f : WA V W → ℂ} :
    IsPolFock (D := w.D Z) ψ θ V W A B f ↔ IsPolFock (D := w.D (setDivZ Z N h)) ψ θ V W A B f :=
  ⟨fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩,
   fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩⟩

@[reducible] def besDatTr {A B : TH.HSp (w.D Z)} {ι : A.V →ₗ[(w.D Z).host.E] B.V} (d : BesDat (D := w.D Z) A B ι) :
    BesDat (D := w.D (setDivZ Z N h)) A B ι := { d with }



def thetaTiedTr {X : ThetaX (w.D Z)} (T : ThetaTied (w.D Z) X) : ThetaTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) :=
  { T with ev_aut := fun V F => (isAutFun_tr w Z N h).1 (T.ev_aut V F) }



def weilTiedTr {X : ThetaX (w.D Z)} {T : ThetaTied (w.D Z) X} (Wl : WeilTied (w.D Z) X T) :
    WeilTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) (thetaTiedTr w Z N h T) :=
  { Wl with
    evS_range := fun V W hne => (Wl.evS_range V W hne).trans (Set.ext fun _ => isThetaFun_tr w Z N h)
    om_tw := { Wl.om_tw with } }



theorem weilTiedEq_tr {X : ThetaX (w.D Z)} {T : ThetaTied (w.D Z) X} {Wl : WeilTied (w.D Z) X T} (e : WeilCompatibleEquivariance Wl) :
    WeilCompatibleEquivariance (weilTiedTr w Z N h Wl) :=
  { e with
    evS_range := fun V W hr => (e.evS_range V W hr).trans (Set.ext fun _ => isThetaFun_tr w Z N h)
    om_tw := { e.om_tw with } }



def allTiedTr {X : ThetaX (w.D Z)} {A : TH.ProvA} (a : AllTied (w.D Z) X A) : AllTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) A where
  T := thetaTiedTr w Z N h a.T
  sm := ⟨a.sm.1, fun θ hθ V hV => (a.sm.2 θ hθ V hV).trans (Set.ext fun _ => isAutFunSm_tr w Z N h)⟩
  ty := { a.ty with }
  W := weilTiedTr w Z N h a.W
  unr := a.unr
  kf := { a.kf with
    kfin := ⟨a.kf.kfin.1, fun θ hθ V W h1 h2 h3 Φ => (a.kf.kfin.2 θ hθ V W h1 h2 h3 Φ).trans (isPolFock_tr w Z N h)⟩ }
  phiUp := a.phiUp
  B := { a.B with dat := fun A B ι ho p => besDatTr w Z N h (a.B.dat A B ι ho p) }
  real := { a.real with }
  prov := { a.prov with }


end


theorem thT_setDiv {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)}
    (n : NchT w Z Wt nch) (th : ThetaX (w.D Z))
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    ThT n th →
      let moved : NchT w (setDivZ Z N h) Wt { nch with } :=
        { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }
      Nonempty (ThT moved (thTrZ w Z N h th)) := by
  intro t
  exact ⟨{ provA := t.provA
           all := allTiedTr w Z N h t.all
           weq := weilTiedEq_tr w Z N h t.weq
           chr := { t.chr with }
           same := { t.same with }
           std := t.std
           io := t.io }⟩

end GlobalTheory.Mem.Top.Bl.ThTTr
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl.RowWt

theorem fockDeg_cast (D : D7) (h : DV.KapDef D) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ D.R.m) :
    ((fockDeg D n : ℤ) : ℚ) = ∑ τ, (∑ a : Fin (D.R.sigW n).1, |DV.aPlusQ D n τ a| +
      ∑ c : Fin (D.R.sigW n).2, |DV.aMinusQ D n τ c|) := by
  unfold fockDeg
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [(h n h1 h2 τ).1 a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h n h1 h2 τ).2 c, abs_neg]

theorem fockDeg_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z Z' : w.Lt)
    (h : DV.KapDef (w.D Z)) (h' : DV.KapDef (w.D Z')) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ (w.D Z).R.m) :
    fockDeg (w.D Z) n = fockDeg (w.D Z') n := by
  have e := fockDeg_cast (w.D Z) h n h1 h2
  have e' := fockDeg_cast (w.D Z') h' n h1 h2
  exact_mod_cast e.trans e'.symm

theorem forcedContent_eq_over_same_choices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt), DV.KapDef (w.D Z) →
    DV.KapDef (w.D Z') → F0K K.s (w.D Z) = F0K K.s (w.D Z') := by
  intro K B f T w Z Z' h h'
  funext y j
  have hT : FTypeG (w.D Z) (j.1 + 1) = FTypeG (w.D Z') (j.1 + 1) := by
    unfold FTypeG
    rw [fockDeg_eq w Z Z' h h' (j.1 + 1) (Nat.succ_pos _) j.2]
  unfold F0K FK
  rw [hT]
  rfl

end GlobalTheory.Mem.Top.Bl.RowWt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem mem_conjPl_iff {K : Type} [Field K] [StarRing K] (Q : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    y ∈ (Formalism.DivisionValues.conjPl Q).asIdeal ↔ (Formalism.DivisionValues.cO K).symm y ∈ Q.asIdeal := by
  show y ∈ Ideal.map (Formalism.DivisionValues.cO K) Q.asIdeal ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, (Formalism.DivisionValues.cO K).apply_symm_apply y⟩

theorem coe_cO {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : ((Formalism.DivisionValues.cO K y : 𝓞 K) : K) = star (y : K) := rfl

theorem coe_cO_symm {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : (((Formalism.DivisionValues.cO K).symm y : 𝓞 K) : K) = star (y : K) := by
  have h := congrArg (fun u : 𝓞 K => (u : K)) ((Formalism.DivisionValues.cO K).apply_symm_apply y)
  simp only [coe_cO] at h
  rw [← h, star_star]

theorem over_conjPl {D D' : D7} {P : HeightOneSpectrum (𝓞 D.what₂.LL)} {P' : HeightOneSpectrum (𝓞 D'.what₂.LL)}
    (h : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL)
    (hx : D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL)) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x' ∈ (Formalism.DivisionValues.conjPl P').asIdeal := by
  rw [mem_conjPl_iff, mem_conjPl_iff]
  apply h
  rw [coe_cO_symm, coe_cO_symm, D.starLL_cx, D'.starLL_cx, hx]

theorem mem_zeroContentPlaces_iff_over_of_nonvanishing {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (hm : X.toD7.R.m = X'.toD7.R.m)
    (hN : ∀ (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m), (j : ℕ) = j' →
      ∀ (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL)),
        (∀ (x : 𝓞 X.toD7.what₂.LL) (x' : 𝓞 X'.toD7.what₂.LL),
          X.toD7.what₂.embLL (x : X.toD7.what₂.LL) = X'.toD7.what₂.embLL (x' : X'.toD7.what₂.LL) → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
        (NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P'))
    (v : X.B.places.Pl) (v' : X'.B.places.Pl) (hB : Below X.toD7 X'.toD7 v v') :
    v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 (fun _ _ => 0) := by
  have hB' := over_conjPl (D := X.toD7) (D' := X'.toD7) hB
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, hm ▸ j.2⟩, ?_⟩
    exact hj.imp (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB).1 h) (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB').1 h)
  · rintro ⟨j', hj⟩
    refine ⟨⟨j', hm.symm ▸ j'.2⟩, ?_⟩
    exact hj.imp (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB).2 h) (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB').2 h)

theorem nzAt_iff_of {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m)
    (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL))
    (hI : (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 P ≠ 0 ↔
      (s0Of z'.R z'.F).Iw j' (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0 P' ≠ 0)
    (hJ : Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) P
          (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ↔
      Formalism.DivisionValues.jw (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) P'
                (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) ≠ 0) :
    NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P' := by
  unfold NzAt
  exact or_congr hI (or_congr hJ Iff.rfl)

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.Top.Bl

theorem below_of_overOne : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  intro D D' hsub v v₁ v₂ h12 hb x x' hxx'
  rw [hb x x' hxx']
  obtain ⟨y, hy, hye⟩ := hsub (x : D.what₂.LL)
  have hyx : y = (x' : D'.what₂.LL) := D'.what₂.embLL.injective (hye.trans hxx')
  have hint : IsIntegral ℤ (⟨(x' : D'.what₂.LL), hyx ▸ hy⟩ : ↥D'.LL0) :=
    (isIntegral_algebraMap_iff ).1 (RingOfIntegers.isIntegral_coe x')
  let z : 𝓞 ↥D'.LL0 := ⟨⟨(x' : D'.what₂.LL), hyx ▸ hy⟩, hint⟩
  have hz : algebraMap (𝓞 ↥D'.LL0) (𝓞 D'.what₂.LL) z = x' := by
    apply RingOfIntegers.ext
    rfl
  rw [← hz, ← GlobalTheory.TwistChoice.val_pos_iff_mem, ← GlobalTheory.TwistChoice.val_pos_iff_mem]
  exact h12 z

end GlobalTheory.Mem.Top.Bl
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Db.DivTr

open Formalism.L2.Forms GlobalTheory.Mem.Top.ColOwe

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)



def atTTS {u : D.what₂.Word} (A : AtTTied (D := D) u) : AtTTied (D := setDiv D N h) u := { A with }



def forms0S {u : D.what₂.Word} (F : Forms0 D u) : Forms0 (setDiv D N h) u :=
  { F with
    atT := atTTS N h F.atT
    cls0 := { F.cls0 with }
    val0 := { F.val0 with }
    lv0 := { F.lv0 with } }



def herm0S (H : Formalism.L2.Herm.Herm0 D) : Formalism.L2.Herm.Herm0 (setDiv D N h) := { H with }



def fullS (X : Formalism.L2.Herm.FullTiedS D) : Formalism.L2.Herm.FullTiedS (setDiv D N h) :=
  { X with
    base := { X.base with }
    atT := fun u => { X.atT u with }
    ad := { X.ad with } }


theorem fullS_to0 (X : Formalism.L2.Herm.FullTiedS D) : (fullS N h X).to0 = herm0S N h X.to0 := rfl



def gS {Gt : GatTies D} {c : LatCmp D} (g : Formalism.L2.G.GroupCompatibilityAll D Gt c) :
    Formalism.L2.G.GroupCompatibilityAll (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) where
  herm := herm0S N h g.herm
  forms := fun u => forms0S N h (g.forms u)
  cmp := { g.cmp with }
  ring := g.ring
  gat := g.gat

end Gen

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

-- Build the transported records at the same index used by the column data.

def fullSZ (X : Formalism.L2.Herm.FullTiedS (w.D Z)) :
    Formalism.L2.Herm.FullTiedS (w.D (setDivZ Z N h)) :=
  { X with
    base := { X.base with }
    atT := fun u => { X.atT u with }
    ad := { X.ad with } }


def forms0SZ {u : B.Word} (F : Forms0 (w.D Z) u) :
    Forms0 (w.D (setDivZ Z N h)) u :=
  { F with
    atT := atTTRe (setDivZ Z N h) F.atT
    cls0 := clsRe (setDivZ Z N h) F.cls0
    val0 := valRe (setDivZ Z N h) F.val0
    lv0 := lvRe (setDivZ Z N h) F.lv0 }


theorem fullS_cols (X : Formalism.L2.Herm.FullTiedS (w.D Z)) :
    (fullSZ w Z N h X).cols = hermRe (setDivZ Z N h) X.cols := rfl


theorem colsRe_to0S (C : ColsTiedSym (w.D Z)) (u : B.Word) :
    ((colsRe (setDivZ Z N h) C).forms u).to0 = forms0SZ w Z N h (C.forms u).to0 := rfl



theorem stdC_tr (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C) :
    TC.StdC w.I w.l (setDivZ Z N h) (colsRe (setDivZ Z N h) C) := fun u =>
  { hC u with gl := { (hC u).gl with } }



def colTTr (t : ColT w Z) : ColT w (setDivZ Z N h) where
  C := colsRe (setDivZ Z N h) t.C
  std := stdC_tr w Z N h t.C t.std
  stdLv := fun u => t.stdLv u
  full := ⟨fullSZ w Z N h t.full.1,
    (fullS_cols w Z N h t.full.1).trans (congrArg (hermRe (setDivZ Z N h)) t.full.2)⟩
  stdDt := t.stdDt
  Gt := { t.Gt with }
  cmp := { t.cmp with }
  g :=
    { herm := { t.g.herm with }
      forms := fun u => forms0SZ w Z N h (t.g.forms u)
      cmp := { t.g.cmp with }
      ring := t.g.ring
      gat := t.g.gat }
  herm_eq := congrArg
    (fun H : Formalism.L2.Herm.Herm0 (w.D Z) =>
      ({ H with } : Formalism.L2.Herm.Herm0 (w.D (setDivZ Z N h)))) t.herm_eq
  forms_eq := funext fun u =>
    (congrArg (forms0SZ w Z N h) (congrFun t.forms_eq u)).trans (colsRe_to0S w Z N h t.C u).symm
  gpl := t.gpl

end GlobalTheory.Mem.Db.DivTr

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.finrank_baseRows_isotypic_eq_goodForms_isotypic : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → ∀ (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  first | exact @GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | exact GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | (intros; apply GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL <;> assumption)
end
