module

public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
public import Formalism.SharpRestriction.GrowthBounds.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.OrbitOfPts
public import Formalism.LocalToGlobal.GroupLattices.ClassLocalOfEq
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.HermitianColumns.TiedQC

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cast

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R}

def castCls {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) (c : C.cls j) : C'.cls j := h ▸ c

theorem castCls_inj {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) : Function.Injective (castCls h j) := by
  subst h; exact fun _ _ h => h

theorem castCls_surj {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) : Function.Surjective (castCls h j) := by
  subst h; exact fun c => ⟨c, rfl⟩

theorem castCls_card {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) (c : C.cls j) :
    Nat.card (C'.stab j (castCls h j c)) = Nat.card (C.stab j c) := by
  subst h; rfl

end Cast

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

structure LabIn (I : CmpJIn Tw u μ w h Lv) where
  onCh : ∀ j hj, (I.at' j hj).C = D.chTw u μ
  chX : ∀ j hj, ChX (I.at' j hj).st
  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m
  c0 : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv
  fill : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j
  rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j
  dgam : (D.chTw u μ).DGam ∣ (D.mem u).C.DGam

variable {I : CmpJIn Tw u μ w h Lv}

def clsAt (X : LabIn I) (H : CmpJHyp c I) : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j
  | 0 => X.c0.cls
  | j + 1 => fun a L =>
    if hj : j + 1 ≤ D.R.m then castCls (X.onCh j hj) (j + 1) (clsOf (S := (I.at' j hj).st) (H.core j hj) a L)
    else X.fill (j + 1) (by omega) a

theorem clsAt_succ (X : LabIn I) (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1)) (L : (Fl.Pj (j + 1)).Tup) :
    clsAt X H (j + 1) a L = castCls (X.onCh j hj) (j + 1) (clsOf (S := (I.at' j hj).st) (H.core j hj) a L) := dif_pos hj

def levelChartElement (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1)) (L : (Fl.Pj (j + 1)).Tup) :
    GL (Fin (D.R.N (j + 1))) D.host.E := gam0 (S := (I.at' j hj).st) (H.core j hj) a L

def labAt (X : LabIn I) (H : CmpJHyp c I) : KerLabelsMu Tw u μ w h Lv where
  fl_t := X.fl_t
  fl_m := X.fl_m
  cls := clsAt X H
  cls_iff := fun j hj a a' L L' hL hL' => by
    cases j with
    | zero => exact X.c0.cls_iff a a' L L' hL hL'
    | succ j =>
      rw [clsAt_succ X H j hj, clsAt_succ X H j hj, (castCls_inj _ _).eq_iff]
      exact clsOf_iff (S := (I.at' j hj).st) (H.core j hj) (X.chX j hj) a a' L L' hL hL'
  cls_surj := fun j hj x => by
    cases j with
    | zero => exact X.c0.cls_surj x
    | succ j =>
      obtain ⟨x0, rfl⟩ := castCls_surj (X.onCh j hj) (j + 1) x
      obtain ⟨a, L, hL, e⟩ := clsOf_surj (S := (I.at' j hj).st) (H.core j hj) x0
      exact ⟨a, L, hL, by rw [clsAt_succ X H j hj]; exact congrArg _ e⟩
  stab_zero := X.c0.stab_zero
  stab_dvd := fun j hj a L hL => by
    cases j with
    | zero =>
      have e : Nat.card {γ : (Lv.lev 0 a).Γ // (Lv.lev 0 a).smul γ L = L} = 1 := X.c0.stab_zero a L hL
      rw [e]
      exact ⟨Nat.one_pos, one_dvd _⟩
    | succ j =>
      have e : Nat.card ((D.chTw u μ).stab (j + 1) (clsAt X H (j + 1) a L)) =
          Nat.card {γ : (Lv.lev (j + 1) a).Γ // (Lv.lev (j + 1) a).smul γ L = L} := by
        rw [clsAt_succ X H j hj, castCls_card]
        exact clsOf_card (S := (I.at' j hj).st) (H.core j hj) (X.chX j hj) a L hL
      rw [← e]
      exact ⟨Nat.card_pos, ((D.chTw u μ).dvd_DGam (j + 1) hj _).trans X.dgam⟩
  rat := X.rat
  stab_eq := fun j h1 hj a L hL => by
    cases j with
    | zero => omega
    | succ j =>
      rw [clsAt_succ X H j hj, castCls_card]
      exact clsOf_card (S := (I.at' j hj).st) (H.core j hj) (X.chX j hj) a L hL

abbrev chainAt (H : CmpJHyp c I) (Gt : GatTies D) : Chain Lv := chainMu (stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt).up

def kaAt (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) : TwTie.KerAtMu D c Tw u μ w h (chainAt H Gt) :=
  kerAtMu_cmpJ (labAt X H) H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt

def kaAtAny (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv)
    (hCh : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
      (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) →
      (stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt).up.cmp (j + 1) y = Ch.Kz j ((stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt).up.cmp j x)) :
    TwTie.KerAtMu D c Tw u μ w h Ch :=
  kerAtMu_any (labAt X H) H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt Ch hCh

theorem kaAt_cls (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) : (kaAt X H Gt).cls = clsAt X H := by
  simp [kaAt, kerAtMu_cmpJ, kerAtMu, kerAtMu_of, labAt]

theorem kaAtAny_cls (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv) (hCh) :
    (kaAtAny X H Gt Ch hCh).cls = clsAt X H := by
  simp [kaAtAny, kerAtMu_any, labAt]

theorem kaAt_cmp (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) (x : ((Tw.fm u μ).lat (j + 1)).V) :
    (kaAt X H Gt).cmp (j + 1) x = (I.at' j hj).st.cmpJ (c.embW u w h) ((I.at' j hj).eps.symm x) :=
  kerAtMu_cmpJ_cmp (labAt X H) H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt j hj x

theorem kaAt_pt (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (a0 : (I.at' j hj).st.cmpt β)
    (L : (Fl.Pj (j + 1)).Tup) (g : ∀ v, GL (Fin ((Fl.Pj (j + 1)).m + 1)) ((Fl.Pj (j + 1)).Qq v))
    (hL : ∀ v, L v = colSpan ((Fl.Pj (j + 1)).W v) (g v : Matrix (Fin ((Fl.Pj (j + 1)).m + 1)) (Fin ((Fl.Pj (j + 1)).m + 1))
      ((Fl.Pj (j + 1)).Qq v)))
    (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hx : ((I.at' j hj).st.loc β).IsPt a0 g x.1) :
    ∃ (hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L) = β)
      (κ : ((I.at' j hj).st.K β).lev.U),
      levelChartElement H j hj ((I.at' j hj).st.eC ⟨β, a0⟩) L ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) ∧
      x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (levelChartElement H j hj ((I.at' j hj).st.eC ⟨β, a0⟩) L) *
        (((I.at' j hj).st.K β).y ⟨_, hc⟩).1 * κ.1 := by
  have hLt : (Fl.Pj (j + 1)).IsLatTup L := isLatTup_of_bases (G := gatJ Lv (j + 1)) L g hL
  have hs := cg_spec (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L hLt
  have hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L) = β := by
    rw [hs.chart, Equiv.symm_apply_apply]
  obtain ⟨κ, e⟩ := hs.pt (H.core j hj) hc g hL x hx
  exact ⟨hc, κ, hs.mem, e⟩

section OnTw

variable {st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))}

end OnTw

section Yb

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
  {st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))}

variable {T}

end Yb

end Formalism.MainNotions.G.KAat

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

section One

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p} {cl : Type}

structure OneHyp (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop where
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S))
  good : LocGood σ J A
  int : LocInt A
  hypP : LocHyp S A
  hypC : LocHypC S A
  bad_p : ∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal
  actB : A.ActB
  comp : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ (i : G.comp) (γ : GL (Fin n) E)
      (a : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), γ ∈ UJ (σ : E →+* E) J ∧ a ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * A.yG i * a ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) a ∈ S.Uloc w
  gam : ∀ i (γ : (G.lev i).Γ), (A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i ∈
        UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w)
        ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i) ∈ S.Uloc w
  gamU : ∀ i (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J
  inj : ∀ i, Function.Injective (A.gamI i)
  onto : ∀ i, GamOnto S A i
  cinj : CompInj S A

def IsCG1 (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (i : G.comp) (L : G.P.Tup) (c : cl) (γ₀ : GL (Fin n) E) : Prop :=
  ∃ (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (κ₀ : S.U),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ∧
    γ₀ ∈ UJ (σ : E →+* E) J ∧ A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (y c).1 * κ₀.1)

variable {S : StepLevel F E σ J T f bad} {A : LocAt F E n G} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem exists_bases1 (L : G.P.Tup) (hL : G.P.IsLatTup L) : ∃ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  choose g hg using fun v => (isLattice_iff _ (L v)).1 (hL v)
  exact ⟨g, fun v => by rw [hg v, colSpan_eq]⟩

theorem isLatTup_of_bases1 (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) : G.P.IsLatTup L :=
  fun v => (isLattice_iff _ (L v)).2 ⟨g v, by rw [hL v, colSpan_eq]⟩

theorem exists_isCG1_bases (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) :
    ∃ c γ₀, IsCG1 S A y i L c γ₀ := by
  obtain ⟨c, γ₀, κ₀, hγ₀, hpt⟩ := ptEx_of H.good S y H.y_bij.2 i g
  exact ⟨c, γ₀, g, κ₀, hL, hγ₀, hpt⟩

theorem exists_isCG1 (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) : ∃ c γ₀, IsCG1 S A y i L c γ₀ := by
  obtain ⟨g, hg⟩ := exists_bases1 L hL
  exact exists_isCG1_bases H i L g hg

theorem IsCG1.cls_eq (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c c' : cl} {γ₀ γ₁ : GL (Fin n) E}
    (h : IsCG1 S A y i L c γ₀) (h' : IsCG1 S A y i L c' γ₁) : c = c' := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  obtain ⟨g', κ₁, hL', hγ', hpt'⟩ := h'
  exact cls_unique H.good H.int H.hypP H.bad_p y H.y_bij.1 i L g g' hL hL' c c' γ₀ γ₁ hγ hγ' κ₀ κ₁ hpt hpt'

theorem IsCG1.mem {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀) :
    γ₀ ∈ UJ (σ : E →+* E) J := by
  obtain ⟨g, κ₀, -, hγ, -⟩ := h
  exact hγ

theorem IsCG1.smul (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E}
    (h : IsCG1 S A y i L c γ₀) (γ : (G.lev i).Γ) : IsCG1 S A y i ((G.lev i).smul γ L) c (A.gamI i γ * γ₀) := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  obtain ⟨κ₁, h1⟩ := pt_smul H.good H.actB H.gam i g _ γ₀ κ₀ hpt γ
  exact ⟨_, κ₁, fun v => smul_colSpan i γ L g hL v, Subgroup.mul_mem _ (H.gamU i γ) hγ, h1⟩

theorem IsCG1.orbit (H : OneHyp S A y) {i i' : G.comp} {L L' : G.P.Tup} {c : cl} {γ₀ γ₁ : GL (Fin n) E}
    (h : IsCG1 S A y i L c γ₀) (h' : IsCG1 S A y i' L' c γ₁) : i = i' ∧ ∃ γ : (G.lev i).Γ, L' = (G.lev i).smul γ L := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  obtain ⟨g', κ₁, hL', hγ', hpt'⟩ := h'
  obtain ⟨rfl, γ, -, hγL⟩ := orbit_of_pts H.good H.int H.hypC H.actB H.gam H.cinj H.onto i i' L L' g g' hL hL' _ γ₀ γ₁ hγ hγ' κ₀ κ₁
    hpt hpt'
  exact ⟨rfl, γ, hγL⟩

theorem IsCG1.pt (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀)
    (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hx : A.IsPt i g x.1) :
    ∃ κ : S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (y c).1 * κ.1 := by
  obtain ⟨g', κ₀, hL', hγ, hpt⟩ := h
  obtain ⟨κ, e1, -⟩ := ptOne_of S H.int H.hypP H.bad_p i L g' g
    ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ) (y c).2) (U_le κ₀.2)⟩ x hL' hL hpt hx
  refine ⟨κ₀ * κ, ?_⟩
  rw [e1]
  show _ * _ * _ * _ = _ * _ * (κ₀.1 * κ.1)
  group

theorem exists_isCG1_of_oneHyp (H : OneHyp S A y) (c : cl) : ∃ i L γ₀, G.P.IsLatTup L ∧ IsCG1 S A y i L c γ₀ := by
  obtain ⟨i, g, γ, κ, hγ, hpt⟩ := ptAll_of H.good S y H.comp c
  exact ⟨i, fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)), γ,
    isLatTup_of_bases1 _ g fun _ => rfl, g, κ, fun _ => rfl, hγ, hpt⟩

theorem IsCG1.card (H : OneHyp S A y) {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J) (hsinj : ∀ c, Function.Injective (stabI c))
    (hrange : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom)
    {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀) :
    Nat.card (stab c) = Nat.card {γ : (G.lev i).Γ // (G.lev i).smul γ L = L} := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  exact card_eq H.good H.int H.hypP H.hypC H.bad_p H.actB H.gam H.gamU i (H.inj i) (H.onto i) L g hL y stabI hsinj hrange c γ₀ hγ κ₀ hpt

theorem cl_nonempty (H : OneHyp S A y) (i : G.comp) : Nonempty cl := by
  obtain ⟨c, -, -⟩ := exists_isCG1_bases H i (fun v => colSpan (G.P.W v) ((1 : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) (fun _ => 1) fun _ => rfl
  exact ⟨c⟩

def cg1 (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) : cl × GL (Fin n) E :=
  @Classical.epsilon _ ((cl_nonempty H i).map fun c => (c, 1)) fun q => IsCG1 S A y i L q.1 q.2

theorem class_map_spec (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    IsCG1 S A y i L (cg1 H i L).1 (cg1 H i L).2 := by
  obtain ⟨c, γ₀, h⟩ := exists_isCG1 H i L hL
  exact @Classical.epsilon_spec _ (fun q : cl × GL (Fin n) E => IsCG1 S A y i L q.1 q.2) ⟨(c, γ₀), h⟩

theorem class_map_fst_eq (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀) :
    (cg1 H i L).1 = c := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := id h
  exact (class_map_spec H i L (isLatTup_of_bases1 L g hL)).cls_eq H h

def localClassDataOfTrivialStabilizers (H : OneHyp S A y) {X : Type} (e : cl ≃ X) {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J) (hsinj : ∀ c, Function.Injective (stabI c))
    (hrange : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom)
    (htriv : ∀ c, Nat.card (stab c) = 1) : Formalism.L2.G.TwTie0.LocalClassData G X where
  cls := fun i L => e (cg1 H i L).1
  cls_iff := fun i i' L L' hL hL' => by
    rw [e.injective.eq_iff]
    constructor
    · intro h
      have h1 := class_map_spec H i L hL
      have h2 := class_map_spec H i' L' hL'
      rw [← h] at h2
      exact h1.orbit H h2
    · rintro ⟨rfl, γ, rfl⟩
      exact (class_map_fst_eq H ((class_map_spec H i L hL).smul H γ)).symm
  cls_surj := fun x => by
    obtain ⟨i, L, γ₀, hL, h⟩ := exists_isCG1_of_oneHyp H (e.symm x)
    exact ⟨i, L, hL, by rw [class_map_fst_eq H h, Equiv.apply_symm_apply]⟩
  stab_zero := fun i L hL => by
    rw [← (class_map_spec H i L hL).card H stabI hsinj hrange]
    exact htriv _

end One

section Lev0

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)}
  {K0 : LevelChart D T bad 0 (Nat.zero_le _) stab lat} {A0 : LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w h)}

def rationalElementZero (H : OneHyp K0.lev A0 K0.y) (a : (D.gat u w h).comp) (L : (D.gat u w h).P.Tup) : GL (Fin (D.R.N 0)) D.host.E :=
  (cg1 H a L).2

def levelZeroClass (H : OneHyp K0.lev A0 K0.y) (a : (D.gat u w h).comp) (L : (D.gat u w h).P.Tup) : cl := (cg1 H a L).1

def clsAt0Of (H : OneHyp K0.lev A0 K0.y) (e : cl ≃ (D.chTw u μ).cls 0) (htriv : ∀ c, Nat.card (stab c) = 1)
    {Fl : Fills (D.gat u w h)} (Lv : Levels Fl) : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv :=
  (localClassDataOfTrivialStabilizers H e K0.stabI K0.stabI_inj K0.stabI_range htriv).toAt0 Lv

theorem pt00 (H : OneHyp K0.lev A0 K0.y) (a : (D.gat u w h).comp) (L : (D.gat u w h).P.Tup)
    (g : ∀ v, GL (Fin ((D.gat u w h).P.m + 1)) ((D.gat u w h).P.Qq v))
    (hL : ∀ v, L v = colSpan ((D.gat u w h).P.W v) (g v : Matrix (Fin ((D.gat u w h).P.m + 1)) (Fin ((D.gat u w h).P.m + 1))
      ((D.gat u w h).P.Qq v)))
    (x : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hx : A0.IsPt a g x.1) :
    rationalElementZero H a L ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧
    ∃ κ : K0.lev.U, x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (rationalElementZero H a L) *
      (K0.y (levelZeroClass H a L)).1 * κ.1 :=
  ⟨(class_map_spec H a L (isLatTup_of_bases1 L g hL)).mem, (class_map_spec H a L (isLatTup_of_bases1 L g hL)).pt H g hL x hx⟩

end Lev0

end Formalism.MainNotions.G.KAat

end
end
