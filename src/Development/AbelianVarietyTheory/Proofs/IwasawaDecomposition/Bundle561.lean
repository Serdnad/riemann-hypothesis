module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem gridKey_heq_of_eq_preData_components (P P' : Pre) (h : P = P') (v : Pl P.host.F) (v' : Pl P'.host.F) (w : Pl P.host.F → Pl P.host.E)
    (w' : Pl P'.host.F → Pl P'.host.E) (c : ℕ → HChar P.host.E) (c' : ℕ → HChar P'.host.E) (hv : HEq v v') (hw : HEq w w')
    (hc : HEq c c') :
    HEq ((v, w v, fun a : Fin P.R.m => c (a.1 + 1)) : GKey P) ((v', w' v', fun a : Fin P'.R.m => c' (a.1 + 1)) : GKey P') := by
  subst h; subst hv; subst hw; subst hc; rfl

theorem gkeyOf_heq {X X' : Stages} {T T' : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {L' : Formalism.IndefR.Links.LevCh X'.toD7 T'} {sc : GlobalTheory.ChiGrid.Consts}
    {G : GridData L sc} {G' : GridData L' sc} (h : GAgree G G') (hp : X'.B.toPre = X.B.toPre) : HEq (gkeyOf G') (gkeyOf G) :=
  gridKey_heq_of_eq_preData_components _ _ hp _ _ _ _ _ _ h.v0 h.w h.chiH

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy



theorem exGrid_of : WeilEx → IsEx → NFAll → NFSq → CarryG → CarryW → CarryS → TrEasy → TrPhase → TrJet → TrBot → TrSq → KeyFin →
    GKeyFin → ExGrid := by
  classical
  intro h1 h2 h3 h4 cG cW cS t1 t2 t3 t4 t5 kF gF
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  obtain ⟨a4, h4⟩ := h4
  refine ⟨max a1 (max a2 (max a3 a4)), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hC)))
  obtain ⟨x4, h4⟩ := h4 ε CF (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hC)))
  refine ⟨max x1 (max x2 (max x3 x4)), fun s he hx P f Ξ hΞ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx))
  have hx4 := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx))
  have per : ∀ (κ : Key P) (γ : GKey P), ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
      ∀ (X : Stages) (f' : Fr X.B.toPre), X.B.toPre = P → HEq f' f → ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks]
        [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F →
        R.C = Fr.at X f' → TwistPlacesOffPrimeQZero R.toLevCh → HEq (keyOf R.toLevCh) κ → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
        HEq (gkeyOf G₀) γ → (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) →
        ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G := by
    intro κ γ
    by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
        (_ : GlobalTheory.SqTop.Rec large₂) (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
        (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks)
        (_ : Algebra Ks X.toD7.what₂.LL) (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A) (G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩),
        HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ ∧ HEq (gkeyOf G₀) γ
    swap
    · exact ⟨∅, by simp, fun X f' a b large₂ c r Γ _ _ Pl0 T A Ks _ _ _ R F d e g i G₀ j _ =>
        absurd ⟨X, f', a, b, large₂, c, r, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, G₀, d, e, g, i, j⟩ H⟩
    obtain ⟨X0, f0, a0, b0, Lg0, rfl, r0, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, G00, d0, e0, g0, i0, j0⟩ := H
    obtain ⟨W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00
    obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00 W0 hW0 S0
    obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
    obtain ⟨N2, hN2, hSq⟩ := h4 _ Lg0 he hx4 r0 T0 R0.toLevCh A0.μ0 d0.core.lev G00
    obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
    obtain ⟨b2⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N2)) ℚ N2) := ⟨Module.finBasis ℚ N2⟩
    refine ⟨(Finset.univ.image fun i => ((b i : N) : ℂ)) ∪ Finset.univ.image fun i => ((b2 i : N2) : ℂ), ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
    intro X f' a b' large₂ hs hr Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i G₀ j hz

    have rng : ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (bK : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K),
        (∀ i, ((bK i : K) : ℂ) ∈ Set.range X.toD7.what₂.embLL) → Set.range (algebraMap K ℂ) ⊆ Set.range X.toD7.what₂.embLL := by
      intro K _ bK hK
      rintro _ ⟨y, rfl⟩

      rw [← bK.sum_repr y, map_sum]
      refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hK i)
    have r1 := rng N b fun i => hz _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have r2 := rng N2 b2 fun i => hz _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
    have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
    have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
      rintro P _ rfl k k' h x hx
      obtain rfl := eq_of_heq h
      exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
    have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
      obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
      exact ⟨t0, h⟩
    choose ι hι using hι
    have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
    have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
      rw [d0.core.lev.xi_base]
      have := (hι A.μ0).1
      rw [d.core.lev.xi_base] at this
      exact eq_of_heq (this.symm.trans (one _ _ hpre)))
    have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
      ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX,
        d.betaX⟩
    obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G00
    obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G00 G hG W0
    obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G00 G hG W0 W hWA S.toGridChoice
    have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
    have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
    rw [hs] at h2'
    obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
    have gk : gkeyOf G = gkeyOf G₀ := eq_of_heq ((gkeyOf_heq hG hpre).trans (j0.trans j.symm))
    refine ⟨G, gk, W, M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hIs', ?_, ?_⟩
    · obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
      have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root,
        t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase, t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios,
        t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
      subst hS2
      exact hAll'.numbersIn.mono r1
    · exact (t5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N2 _ hSq).mono r2
  obtain ⟨𝒦, hK, H⟩ := kF P Ξ hΞ
  obtain ⟨𝒢, hG, HG⟩ := gF P 1
  choose S hS HS using per
  refine ⟨hK.toFinset.biUnion fun κ => hG.toFinset.biUnion fun γ => S κ γ, ?_, ?_⟩
  · intro z hz
    obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨γ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ γ z hz
  intro X f' Ξ' hP hf hΞ' hz large₂ hs hRec Γ _ _ Pl0 T A Ks _ _ _ R F st hCf ho htw G₀
  subst hP
  obtain rfl := eq_of_heq hΞ'
  obtain ⟨κ, hκ, hk⟩ := H X T R.toLevCh A.μ0 rfl st.core.lev htw
  obtain ⟨γ, hγ, hg⟩ := HG X T R.toLevCh _ G₀ rfl rfl
  exact HS κ γ X f' rfl hf large₂ hs hRec Γ Pl0 T A Ks R F st hCf ho hk G₀ hg fun z hz' =>
    hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, Finset.mem_biUnion.2 ⟨γ, hG.mem_toFinset.2 hγ, hz'⟩⟩)

end GlobalTheory.Mem.LiteralAutomorphy

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) :
    NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { x.o.N with ntw := N.tw, nexp := N.ex, nStage_trivialCharacter_coeff_eq := N.h0, nth := N.th, ntwbr := N.br, ntwbr_ind := N.hbr }

def oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : P.q.Over := ⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩

theorem dof_oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : (w.st (oTw x N).Z).toD7 = N.toD7 := rfl

end GlobalTheory.HeightCounting.Up

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SCuspRows

theorem allSt_and' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)


end GlobalTheory.SCuspRows
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up

namespace PointStatements

section Loc

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}

end Loc

theorem allSt_mono {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) (hp : AllSt p) : AllSt q :=
  hp.trans (StepW.of_all fun _ _ _ _ _ _ _ H P x => h _ _ _ _ _ P x (H P x))

theorem allSt_and {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (hp : AllSt p) (hq : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  (StepW.and hp hq).trans (StepW.of_all fun _ _ _ _ _ _ _ H P x => ⟨H.1 P x, H.2 P x⟩)

end PointStatements


end GlobalTheory.HeightCounting.Up

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.ElemAtStates

theorem allSt_and {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)

end GlobalTheory.ElemAtStates
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar




def nOfLay {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : Lay0 (Dof x)) (hZ : L.ZOk) (hE : L.EtaOk) : NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := L.nd, ntw := L.ntw, naut := L.naut, nbc := L.nbc, nexp := L.nexp,
    ntypes := L.ntypes, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq, nth := L.nth, nbr := L.nbr, nbr_ind := L.nbr_ind,
    self_good := L.self_good, ntwbr := L.ntwbr, ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie,
    rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

theorem exists_pq_sel (B : Base) {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) :
    ∃ Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield B.host.E)) → PlE B.host,
      (∀ v, NG.OverPl (Pq v) v) ∧ Set.range Pq = Set.range I.sel :=
  ⟨I.sel, fun v => hI.sel_ok v, rfl⟩

end GlobalTheory.HeightCounting.Up

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory



open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.BigTop.Fun in
theorem Mem.LiteralAutomorphy.trSq_holds : GlobalTheory.Mem.LiteralAutomorphy.TrSq := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ hs
  obtain ⟨⟨hpre, -, -, ⟨f, f', hff, hC, hC'⟩, hbase, hxi, -, -⟩, hg, -, -⟩ := h
  clear S S' W W'
  obtain ⟨B, C₁, W₁, V₁, S₁, N₁, G₁⟩ := X
  obtain ⟨B', C₂, W₂, V₂, S₂, N₂, G₂⟩ := X'
  cases B; cases B'
  dsimp only at hpre
  subst hpre
  obtain rfl := eq_of_heq hff
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hx : L'.xiH μ₀' = L.xiH μ₀ := by have := eq_of_heq (hxi μ₀'); rwa [hbase] at this
  have e_levQ : levQ G'.pl = levQ G.pl := by
    unfold levQ Places.S0 condExp; rw [hv0]; exact (Eq.refl (levQ G.pl))
  have e_condE : SqNum.condE G'.pl = SqNum.condE G.pl := by
    unfold SqNum.condE Places.S0 condExp; rw [hv0, hw]; exact (Eq.refl (SqNum.condE G.pl))
  have e_condF : condF G'.pl = condF G.pl := by
    unfold condF Places.S0 condExp; rw [hv0]; exact (Eq.refl (condF G.pl))
  have hmu : L'.C.mu0 = L.C.mu0 := by rw [hC, hC']; exact (Eq.refl f'.mu0)
  have heta : L'.C.eta = L.C.eta := by rw [hC, hC']; exact (Eq.refl f'.eta)
  have hd1 : L'.C.del = L.C.del := by rw [hC, hC']; exact (Eq.refl f'.del)
  have hd2 : L'.C.del' = L.C.del' := by rw [hC, hC']; exact (Eq.refl f'.del')
  have e_nu : ∀ i j, nuH G' μ₀' i j = nuH G μ₀ i j := by
    intro i j; unfold nuH; rw [hmu, hx, hchi]; exact (Eq.refl (nuH G μ₀ i j))
  have e_beta : ∀ i j, betaH G' i j = betaH G i j := by
    intro i j; unfold betaH; rw [heta, hchi]; exact (Eq.refl (betaH G i j))
  have e_alpha : ∀ i j, alphaH L' μ₀' i j = alphaH L μ₀ i j := by
    intro i j; unfold alphaH; rw [hmu, hx, heta]; exact (Eq.refl (alphaH L μ₀ i j))
  have e_del : ∀ c, delOf L' c = delOf L c := by
    intro c; unfold delOf; rw [hd1, hd2]; exact (Eq.refl (delOf L c))
  have eT : ∀ i j s χ x, IsTor G' i j s χ x ↔ IsTor G i j s χ x := by
    intro i j s χ x; unfold IsTor; rw [e_condF]; exact (Iff.refl (IsTor G i j s χ x))

  let hk1 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt1 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk1 w.chV, chV' := hk1 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt1 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt1 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  let hk2 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt2 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk2 w.chV, chV' := hk2 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt2 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt2 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  have btr1 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q), IsBottom G μ₀ i j (SqNum.condE G.pl) P P' →
        IsBottom G' μ₀' i j (SqNum.condE G'.pl) (pt1 P) (pt1 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨(h1), ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_beta, e_nu]; exact (h2)
    · rw [e_alpha, e_nu]; exact (h3)
    · rw [e_condE]; exact (h4)
    · rw [e_condE]; exact (h5)
    · rw [e_condE]; exact (h6)

  have btr2 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q), IsBottom G' μ₀' i j (SqNum.condE G'.pl) P P' →
        IsBottom G μ₀ i j (SqNum.condE G.pl) (pt2 P) (pt2 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    rw [e_beta, e_nu] at h2
    rw [e_alpha, e_nu] at h3
    rw [e_condE] at h4 h5 h6
    exact ⟨(h1), (h2), (h3), (h4), (h5), (h6)⟩
  refine ⟨fun hb => ?_, fun i j s c x y h1 h2 h3 h4 => ?_⟩
  · obtain ⟨δ, t0, hb⟩ := hb
    rw [e_levQ] at hb
    obtain ⟨δ', t0', hb'⟩ := hs.norms ⟨δ, t0, fun ij => by
      obtain ⟨P, P', hP, -, -⟩ := hb ((ij))
      exact ⟨pt2 P, pt2 P', btr2 ((ij.1)) ((ij.2)) P P' hP, trivial, trivial⟩⟩
    refine ⟨δ', t0', fun ij => ?_⟩
    rw [e_levQ]
    obtain ⟨P, P', hP, n1, n2⟩ := hb' ((ij))
    exact ⟨pt1 P, pt1 P', btr1 ij.1 ij.2 P P' hP, (n1), (n2)⟩
  · rw [eT, e_nu] at h3
    rw [eT, e_nu, e_del] at h4
    exact hs.toric ((i)) ((j)) s c x y h1 ((h2)) ((h3)) ((h4))

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

theorem kept_trans_layer {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''} (h : Kept c c') (h' : Kept c' c'') :
    Kept c c'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.forms.Fm.trans h'.forms.Fm, h.forms.acgFm.trans h'.forms.acgFm, h.forms.modFmK.trans h'.forms.modFmK, h.forms.modFmO.trans h'.forms.modFmO, h.forms.actG.trans h'.forms.actG, h.forms.U.trans h'.forms.U, h.forms.psiU.trans h'.forms.psiU, h.forms.eAlg.trans h'.forms.eAlg, h.forms.Dat.trans h'.forms.Dat, h.forms.th.trans h'.forms.th, h.forms.lev.trans h'.forms.lev, h.forms.thPsi.trans h'.forms.thPsi, h.forms.MtV.trans h'.forms.MtV, h.forms.acgMt.trans h'.forms.acgMt, h.forms.modMtK.trans h'.forms.modMtK, h.forms.modMtO.trans h'.forms.modMtO, h.forms.MtLat.trans h'.forms.MtLat, h.forms.thP.trans h'.forms.thP, h.forms.hkF.trans h'.forms.hkF⟩,
    h.br.trans h'.br, h.twI.trans h'.twI, h.sd.trans h'.sd, h.Q.trans h'.Q, h.k.trans h'.k, h.psi.trans h'.psi⟩


end GlobalTheory.HeightCounting.Up
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.HeightCounting.Up



theorem kept_trans {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''}
    (h : Kept c c') (h' : Kept c' c'') : Kept c c'' := by
  obtain ⟨g1, s1, f1, b1, t1, d1, q1, k1, p1⟩ := h
  obtain ⟨g2, s2, f2, b2, t2, d2, q2, k2, p2⟩ := h'
  refine ⟨?_, ?_, ?_, b1.trans b2, t1.trans t2, d1.trans d2, q1.trans q2, k1.trans k2, p1.trans p2⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := g1
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := g2
    exact ⟨a1.trans e1, a2.trans e2, a3.trans e3, a4.trans e4, a5.trans e5, a6.trans e6, a7.trans e7, a8.trans e8⟩
  · cases s1; cases s2; constructor <;> (apply HEq.trans <;> assumption)
  · cases f1; cases f2; constructor <;> (apply HEq.trans <;> assumption)

end GlobalTheory.HeightCounting.Up

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.PositiveBaseCharge

theorem q0_pos_allSt : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) :=
  StepW.of_all fun _ _ _ _ _ _ _ _ _ x => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (Dof x)).1.pos

end GlobalTheory.HeightCounting.Up.PositiveBaseCharge
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem nfSq_of_fieldDat : GlobalTheory.NormSum.IntSt → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.BotSmall → NFSq := by
  intro hI hFD hTE hBS
  obtain ⟨CF0, h⟩ := GlobalTheory.SqTop.SqField.gBig_and hFD (GlobalTheory.SqTop.SqField.gBig_and hTE hBS)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ he hx hR T L μ₀ hμ G => ?_⟩
  obtain ⟨⟨_, _, _, _, hΛ⟩, hT, hQ, -, hB⟩ := h C0 le_rfl D large₂ he hx hR T L μ₀ hμ G
  exact GlobalTheory.SqTop.SqField.sqIn_of G μ₀ hI hΛ
    (fun i j s h1 h2 c => let ⟨x, a, b, _, d⟩ := hT i j s h1 h2 c; ⟨x, a, b, d⟩) hQ hB

end GlobalTheory.Mem.LiteralAutomorphy

end
end
