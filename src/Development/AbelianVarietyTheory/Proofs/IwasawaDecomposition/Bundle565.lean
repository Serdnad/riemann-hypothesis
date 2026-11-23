module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOutsideListProd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle445
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle545
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
import Formalism.SharpRestriction.InertJacobiLevels.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem readC_reFace_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp Sp' : ∀ Zs, SPer (Dc Zs))
    (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (kap : ℝ) (lam : type_of% R.lam3)
    (err : type_of% (R.updS kap lam).err0) {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (C : ReadC R (reFace F Dc Sp Zsc) X0 Y)
    (Y₁ : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat F.lv2 X0) (h1 : Y₁.tup = Y.tup) (h2 : HEq Y₁.jA Y.jA) :
    Nonempty (ReadC ((R.updS kap lam).withErr err) (reFace F Dc Sp' Zsc') X0 Y₁) := by
  let F₀ := reFace F Dc Sp Zsc
  let F₁ := reFace F Dc Sp' Zsc'
  let R₁ := (R.updS kap lam).withErr err
  let zs := (R.toCx3 F₀).zs
  have hz : (R₁.toCx3 F₁).zs = zs :=
    (RealDat3.zs_withErr (R := R.updS kap lam) (F := F₁) err).trans
      ((RealDat3.zs_updS (R := R) (F := F₁) kap lam).trans (show (R.toCx3 F₁).zs = zs from rfl))
  have transportPt : ∀ (tp : T → D.what₂.Tup)
      (j : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tp t)), tp = Y.tup → HEq j Y.jA →
      ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc zs).a (C.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 zs).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc zs).Pt (C.wU u) t x f) =
          D.what₂.perCol u (tp t) (D.jN u (C.eNu u x)) (j t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) := by
    intro tp j htp hj
    subst htp
    cases hj
    exact C.pt
  -- Transport the constructor once so its dependent fields share the source subspace.
  have build := ReadC.mk (R := R₁) (F := F₁) (X0 := X0) (Y := Y₁)
  rw [hz] at build
  exact ⟨build C.wU C.bij C.eNu C.NuC C.nu (transportPt Y₁.tup Y₁.jA h1 h2)⟩

end GlobalTheory.Mem.R3

end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem row_mono_id {Bd : GlobalTheory.Fc.BdT} {Q Q₁ : V4.Slot} {Lk Lk₁ : GlobalTheory.Fc.LkT Bd} {H : ∀ 𝒜 : FamClass, GlobalTheory.Fc.RawSel Bd 𝒜 → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hL : ∀ K β c b, Lk₁ K β c b → Lk K β c b)
    (h : GlobalTheory.Fc.Row Q Lk H) : GlobalTheory.Fc.Row Q₁ Lk₁ H :=
  GlobalTheory.Fc.Row.map (fun _ _ _ b => b) hQ (fun K β c b _ t => hL K β c b t) h

theorem largeBaseProperty_anti {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ R : V4.Slot} (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c)
    (h : GlobalTheory.Fc.LargeBaseCondition KP Q R) : GlobalTheory.Fc.LargeBaseCondition KP Q₁ R :=
  GlobalTheory.Fc.eventuallyAllScaleContexts_mono_of_imp (fun _ H => H.imp fun _ _ _ _ t k C W V S N G c q => t k C W V S N G c (hQ _ _ _ _ _ q)) h

theorem eventually_coreProperty_mono_fewerCores {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ Q' Q'₁ : V4.Slot} {r r₁ : V4.Slot → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hQ' : ∀ K X f T c, Q'₁ K X f T c → Q' K X f T c)
    (hr : ∀ S S₁ : V4.Slot, (∀ K X f T c, S₁ K X f T c → S K X f T c) → r S → r₁ S₁)
    (h : GlobalTheory.Fc.Lg1 KP Q Q' r) : GlobalTheory.Fc.Lg1 KP Q₁ Q'₁ r₁ := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, largeBaseProperty_anti hQ hR, hr _ _ (fun _ _ _ _ _ t => ⟨hQ' _ _ _ _ _ t.1, t.2⟩) h⟩

end GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

end GlobalTheory.HeightCounting.Up
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.BlockLiftFrame

open ReciprocityTheory.Aut GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_isCompOf (s : SplitPlace L) {κ : Formalism.AUTREP.GAf L n} (hκ : κ ∈ Umax L n) :
    ∃ y : GL (Fin n) (Os s), IsCompOf s κ y := by
  obtain ⟨y, hy⟩ := GlobalTheory.TSetDoubleCoset.loc_mem_GLint s hκ
  refine ⟨y, fun a c => ?_⟩
  rw [← hy]
  rfl

theorem isCompOf_one_of_not_mem (s : SplitPlace L) {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    (h : s.v ∉ T) {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : IsCompOf s x 1 := by
  have e : s.loc n x = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    have hc : compAt L s.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
      have := congrFun (congrFun (hx s.v h) a) b
      rw [Matrix.map_apply] at this
      rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s _ hc
    rw [map_sub, sub_eq_zero] at h0
    show s.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  intro a c
  rw [e]
  by_cases hac : a = c <;> simp [Matrix.one_apply, hac]

theorem isBlockDiagonal_reduction_of_blockLift_splitPlace (s : SplitPlace L) {r p : ℕ} [NeZero p] (γ : GL (Fin r) (ZMod p)) {κ : Formalism.AUTREP.GAf L n}
    {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) (hl : GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc n κ)) {k : Type} [CommRing k]
    (φ : Os s →+* k) (hφ : IsResidue s φ) (i : ZMod p →+* k) :
    GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (Formalism.UG.bc i γ) (Matrix.GeneralLinearGroup.map φ y) := by
  intro a b
  have hl' := hl a b
  have hyab := hy a b
  show φ (y.val a b) = _
  by_cases hab : a.val < r ∧ b.val < r
  · rw [dite_eq_left hab] at hl' ⊢
    show φ (y.val a b) = i ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩)
    set m : ℕ := ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val with hm
    have h0 : φ (y.val a b - (m : Os s)) = 0 := by
      rw [hφ.ker]
      push_cast
      rw [hyab]
      exact hl'
    rw [map_sub, sub_eq_zero, map_natCast] at h0
    rw [h0, ← map_natCast i m, hm, ZMod.natCast_zmod_val]
  · rw [dite_eq_right hab] at hl' ⊢
    have h1 : ((y.val a b : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = if a = b then 1 else 0 := by
      rw [hyab]; exact hl'
    split_ifs at h1 ⊢ with hab'
    · have h2 : y.val a b = 1 := Subtype.ext (by simpa using h1)
      rw [h2, map_one]
    · have h2 : y.val a b = 0 := Subtype.ext (by simpa using h1)
      rw [h2, map_zero]

end Local

theorem not_mem_gPl_of_twist (D : D7) {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) (s : SplitPlace D.host.E)
    (hs : s.w ∈ Q) : s.v ∉ GlobalTheory.PendOf.gPl D := by
  rintro ⟨kv, hov⟩
  obtain ⟨q, hq, hcard, -, hqg⟩ := (hQ s.w hs).1
  have hg : (D.host.g kv.1 : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have h0 : (D.host.g kv.1 : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    have h1 : ((D.host.g kv.1 : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hov, Ideal.mem_comap, map_natCast]; exact h0
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at h1
    exact h1
  exact GlobalTheory.LevelTypePlace.not_two_primes s.w.asIdeal (D.host.g_prime kv.1) hq (hqg kv.1).symm hg
    (GlobalTheory.LevelTypePlace.natCast_mem_of_card s.w hcard hq.ne_zero)

theorem exists_blockLift (D : D7) {Q Pg : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {G : Type} [Group G]
    (eG : G ≃* G0 Pg D.R.r) (cG : G0 Pg D.R.r ≃* G0g D.nd)
    (hgrp : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
      ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) :
    ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV,
      GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ∧
      ∀ g (s' : SplitPlace D.host.E) (φ : Os s' →+* kP s'.w), IsResidue s' φ →
        (s'.w ∈ Q → ∃ y, IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
        ∀ hP : s'.w ∈ Pg, ∃ y, IsCompOf s' (L g) y ∧
          GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (eG ((eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  obtain ⟨plg, iso, hpl, hg⟩ := hgrp
  obtain ⟨L, hL, hU⟩ := GlobalTheory.LiftStandardGroup.main D D.R.nV (by unfold Ranks.nV; omega)
  refine ⟨L, hL, hU, fun g s' φ hφ => ⟨fun hs => ?_, fun hP => ?_⟩⟩
  · exact ⟨1, isCompOf_one_of_not_mem s' (not_mem_gPl_of_twist D hQ s' hs) (hL g).1, map_one _⟩
  · obtain ⟨y, hy⟩ := exists_isCompOf s' (hU g)
    refine ⟨y, hy, ?_⟩
    have hkv : plg (plg.symm ⟨s'.w, hP⟩) = ⟨s'.w, hP⟩ := plg.apply_symm_apply _
    have key : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (PP : Pg), plg kv = PP →
        ∃ i : ZMod (D.host.g kv.1) →+* kP PP.1, eG ((eG.trans cG).symm g) PP = Formalism.UG.bc i (g kv) := by
      intro kv PP hPP
      subst hPP
      exact ⟨iso kv, by rw [hg, MulEquiv.apply_symm_apply]⟩
    obtain ⟨i, hi⟩ := key _ _ hkv
    rw [hi]
    have hw : s'.w = D.naut.plGw (plg.symm ⟨s'.w, hP⟩).1 (plg.symm ⟨s'.w, hP⟩).2 := by
      rw [← hpl, hkv]
    haveI : NeZero (D.host.g (plg.symm ⟨s'.w, hP⟩).1) := ⟨(D.host.g_prime _).ne_zero⟩
    exact isBlockDiagonal_reduction_of_blockLift_splitPlace s' (g _) hy ((hL g).2 _ s' hw) φ hφ i

end GlobalTheory.BlockLiftFrame

end
end

section

noncomputable section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.SerCopy



namespace GlobalTheory.LayerMove.SerUp

theorem rowPsi_ext {D : D7} {V : HSp D} {n : ℕ} {p q : principalLevelFrame.RowPsi V n} (h : p.ψ = q.ψ) : p = q := by
  cases p; cases q; cases h; rfl

variable {B : GlobalTheory.Mem.Base} {C : Cols B} {W : RowsRest B C} (o : Oth W) (V' : DivStage B C W) (S' : SStage B C W)

def o2 : Oth W := ⟨V', S', o.N, o.G⟩

variable {o} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 o.L.D.what₂.LL G Pl0 I0 (List ℕ) T o.L.D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks o.L.D.what₂.LL] {R : RealDat3 o.L.D A3 Ks}
  {cG : G0 R.Pg o.L.D.R.r ≃* G0g o.L.D.nd} {S : RatDat o.L.D.ntw} {YS : NExpRealS R cG S}
  {v₀ : ∀ (j : Fin o.L.D.R.m) (σ : o.L.D.what₂.LL →+* ℂ), (R.MW j σ).Vec}

set_option hygiene false in
local notation "bb" => Oth.L (o2 o V' S')

variable (YS) in
def ys : @NExpRealS (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S)) :=
  @NExpRealS.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (S :)))
    (fi := (by with_unfolding_all exact (YS.fi :))) (geq := (by with_unfolding_all exact (YS.geq :))) (rho := (by with_unfolding_all exact (YS.rho :))) (chi := (by with_unfolding_all exact (YS.chi :))) (eF := (by with_unfolding_all exact (YS.eF :))) (bsup := (by with_unfolding_all exact (YS.bsup :)))
    (act := (by with_unfolding_all exact (YS.act :)))

def rho (ρ : Setup o.L.D.ntw) : Setup (Late.D bb).ntw := (by with_unfolding_all exact ((seT (o2 o V' S') ρ) :))

theorem good {ρ : Setup o.L.D.ntw} (h : ρ.Good) : (rho V' S' ρ).Good := (by with_unfolding_all exact ((seGood (o2 o V' S') h) :))

theorem pin {ρ : Setup o.L.D.ntw} (p : RealPin R cG ρ) :
    @RealPin (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) (rho V' S' ρ) :=
  @RealPin.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) (rho V' S' ρ)
    ((by with_unfolding_all exact (p.psi :))) ((by with_unfolding_all exact (p.inf :))) ((by with_unfolding_all exact (p.cartT :))) ((by with_unfolding_all exact (p.onbS :))) ((by with_unfolding_all exact (p.onbT :))) ((by with_unfolding_all exact (p.latS :))) ((by with_unfolding_all exact (p.latT :))) ((by with_unfolding_all exact (p.frS :)))
    ((by with_unfolding_all exact (p.frT :))) ((by with_unfolding_all exact (p.vac :))) ((by with_unfolding_all exact (p.Pg :))) ((by with_unfolding_all exact (p.grp :))) ((by with_unfolding_all exact (p.mu0 :))) ((by with_unfolding_all exact (p.eta :))) ((by with_unfolding_all exact (p.delta :))) ((by with_unfolding_all exact (p.deltaPl :)))
    ((by with_unfolding_all exact (p.ap :))) ((by with_unfolding_all exact (p.am :)))

variable (R v₀) in
theorem norm_iff (ρ : Setup o.L.D.ntw) (i : o.L.D.ntw.Tw) (j : Fin o.L.D.R.m) (b : Bool) (ν : ℂ) :
    @IsNorm (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((v₀)) ((j))
      ((rho V' S' ρ).B ((i)) ((j)) b) ν ↔ IsNorm R v₀ (ρ.B i j b) ν := by
  constructor <;> rintro ⟨h0, c, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ <;>
    refine ⟨h0, c, ⟨(by with_unfolding_all exact g), (by with_unfolding_all exact c0R),
      (by with_unfolding_all exact c0L), ?_, (by with_unfolding_all exact u),
      (by with_unfolding_all exact hu), (by with_unfolding_all exact hh)⟩,
      (by with_unfolding_all exact hn)⟩
  have hTie := famTie_imp (a := bb) o.L G _ _ Pl0 T _ _ _ _ _ _ _ _ _ _ _ _ _ g c0R c0L hF
  on_goal 2 =>
    have hTie := famTie_imp (a := o.L) bb G _ _ Pl0 T _ _ _ _ _ _ _ _ _ _ _ _ _ g c0R c0L hF
  -- Both proof terms are fully elaborated. The kernel compares the dependent
  -- level data directly, avoiding the elaborator's repeated unfolding.
  all_goals
    run_tac
      Lean.Elab.Tactic.closeMainGoalUsing `norm_iff fun target _ => do
        let proof ← Lean.Meta.getLocalDeclFromUserName `hTie
        let actual ← Lean.instantiateMVars proof.type
        let target ← Lean.instantiateMVars target
        let context ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
        match Lean.Kernel.isDefEq (← Lean.getEnv) context actual target with
        | .ok true => pure proof.toExpr
        | .ok false => throwError "famTie_imp has type{actual}\nbut the goal is{target}"
        | .error error => throwError (error.toMessageData (← Lean.getOptions))

variable (YS v₀) in
theorem rat_iff {ρ : Setup o.L.D.ntw} (hρ : ρ.Good) (i : o.L.D.ntw.Tw) (j : Fin o.L.D.R.m) (b : Bool) (ν : ℂ) :
    SeriesTie.Rat (good V' S' hρ) (@realRd (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S))
      (ys V' S' YS) ((v₀)) _ (good V' S' hρ) ((i)) ((j)) b ν) ↔ SeriesTie.Rat hρ (realRd YS v₀ hρ i j b ν) :=
  ⟨fun h => @ratT' B C W o (o2 o V' S') _ _ ρ i j b _ (realRd YS v₀ hρ i j b ν) hρ ((by with_unfolding_all exact (h :))),
    fun h => (by with_unfolding_all exact ((@ratT B C W o (o2 o V' S') _ _ ρ i j b _ (realRd YS v₀ hρ i j b ν) hρ h) :))⟩

theorem scalar {ρ : Setup o.L.D.ntw} {hρ : ρ.Good} {i : o.L.D.ntw.Tw} {j : Fin o.L.D.R.m} {b : Bool} {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) :
    @IsScalar (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S))
      (ys V' S' YS) ((v₀)) _ (good V' S' hρ) ((i)) ((j)) b ν :=
  @IsScalar.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (S :)))
      (ys V' S' YS) ((by with_unfolding_all exact (v₀ :))) _ (good V' S' hρ) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b ν h.ne
    (fun h' => (norm_iff V' S' R v₀ ρ i j b _).2 (h.norm (h'.imp fun ν => (norm_iff V' S' R v₀ ρ i j b ν).1)))
    (fun h' => (rat_iff V' S' YS v₀ hρ i j b _).2 (h.rat (h'.imp fun ν h'' =>
      ⟨(norm_iff V' S' R v₀ ρ i j b ν).1 h''.1, (rat_iff V' S' YS v₀ hρ i j b ν).1 h''.2⟩)))

def ex (p : ExportTie YS v₀) :
    @ExportTie (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S)) (ys V' S' YS) ((v₀)) :=
  @ExportTie.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (S :))) (ys V' S' YS) ((by with_unfolding_all exact (v₀ :)))
    (ρ := rho V' S' p.ρ)
    (good := good V' S' p.good)
    (pin := pin V' S' p.pin)
    (vec := (by with_unfolding_all exact (p.vec :)))
    (ν := (by with_unfolding_all exact (p.ν :)))
    (scalar := fun i j b => (by with_unfolding_all exact ((scalar V' S' (p.scalar ((i)) ((j)) b)) : _)))
    (tie := fun i j b => (by with_unfolding_all exact ((cellT (o2 o V' S') (p.tie ((i)) ((j)) b)) : _)))
    (hecke := fun i j b => (by with_unfolding_all exact ((heckeTieT (o2 o V' S') (p.hecke ((i)) ((j)) b)) : _)))
    (univ := (by with_unfolding_all exact (p.univ :)))

end GlobalTheory.LayerMove.SerUp
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
open GlobalTheory.LayerMove
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelRowPin

theorem amb_of_eq {D : D7} {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ} {A : FamIn D.what₂.LL Gp Pl0 T m}
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    {X : RowSide D EE} {Fm Fm' : AmbForm D X} {P : Subgroup Gp} {ψ : P →* D.what₂.LLˣ} {tup tup' : T → D.what₂.Tup}
    {jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)}
    {jA' : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup' t)}
    (hF : Fm = Fm') (h : tup = tup') (hj : HEq jA jA') :
    (∃ J, AmbTie D A X Fm' P ψ tup' jA' J) → ∃ J, AmbTie D A X Fm P ψ tup jA J := by
  subst hF; subst h; cases hj; exact id


end GlobalTheory.Mem.R3.SelRowPin
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

attribute [local instance] GlobalTheory.Mem.R3.TwIn.grp GlobalTheory.Mem.R3.TwIn.fin GlobalTheory.Mem.R3.TwIn.alg

namespace GlobalTheory.Mem.R3.SelRealIn

open Formalism.L2.SG.RowsJoinPinned Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta GlobalTheory.Mem.Top.Bl

section Gen
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem nexp_upd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (n : NExpRealS R cG S)
    (lam : type_of% R.lam3) (err : type_of% R.err0) :
    ∃ (Sx : RatDat D.ntw) (n' : NExpRealS ((R.updS R.kap lam).withErr err) cG Sx), HEq Sx S ∧ HEq n'.eF n.eF ∧ HEq n'.fi n.fi :=
  ⟨S, ⟨n.fi, n.geq, n.rho, n.chi, n.eF, n.bsup, n.act⟩, HEq.rfl, HEq.rfl, HEq.rfl⟩
end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}



end GlobalTheory.Mem.R3.SelRealIn
end
