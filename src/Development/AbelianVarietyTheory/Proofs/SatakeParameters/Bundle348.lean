module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsEqOfSameEigensystemThetaAdjoint
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle839
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle466
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle129
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle339
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle301
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle327
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle329
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle338
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

theorem _root_.GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  first | exact @GlobalTheory.AtG.RX.rowPin_of_rx | exact GlobalTheory.AtG.RX.rowPin_of_rx | (intros; apply GlobalTheory.AtG.RX.rowPin_of_rx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.GlobDet.main | exact GlobalTheory.GlobDet.main | (intros; apply GlobalTheory.GlobDet.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.parts_eq_of_same_eigensystem_thetaAdjoint : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ c c', ∀ w ∈ R.Wc' j c, ∀ w' ∈ R.Wc' j c', LinearMap.adjoint (R.thG j A3.A.μ0) w ≠ 0 → LinearMap.adjoint (R.thG j A3.A.μ0) w' ≠ 0 → labW j pl cW c = labW j pl cW c' → R.Wc' j c = R.Wc' j c' := by
  first | exact @GlobalTheory.Hk3.SepLift.parts_eq_of_labW | exact GlobalTheory.Hk3.SepLift.parts_eq_of_labW | (intros; apply GlobalTheory.Hk3.SepLift.parts_eq_of_labW <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.UnlinkedChars

theorem rc_unlinked_chars : Inputs → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ w A h a ha rc H x n ξ hξ hs hu
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hI.exh (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hI.zel _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hI.zel _ x _ _ hs hs'
  have hL := H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)
  have hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩

  have hlen : ∀ Δ ∈ 𝔪, Δ.len = 1 := by
    intro Δ hΔ
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := by
    intro Δ hΔ
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j) := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨j, rfl⟩
  have hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j) := fun Δ hΔ =>
    hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [hL, segSum]
    congr 1
    apply List.map_congr_left
    intro Δ hΔ
    rw [hlen Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := by
    intro j g
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  refine ⟨?_, fun g => ?_⟩
  · rw [hsum]
    have key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) →
        (sumList (L.map fun Δ => rc Δ.first)).mono0 := by
      intro L
      induction L with
      | nil =>
        intro _
        show (WD.lpZero (h := h)).mono0
        exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl
      | cons Δ L ih =>
        intro hL'
        obtain ⟨j, hj⟩ := hfirst Δ (hL' Δ List.mem_cons_self)
        show (WD.lpSum _ _).mono0
        refine (WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩
        change (rc Δ.first).mono0
        rw [hj]
        exact WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)
    exact key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ
  · rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]
    have r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
      rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)
    rw [r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rfl

end GlobalTheory.RoadU.UnlinkedChars
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

theorem _root_.GlobalTheory.T.kernelClassSums_carry_chainComplexForms : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  first | exact @GlobalTheory.KFiClose.kFi_of_tie | exact GlobalTheory.KFiClose.kFi_of_tie | (intros; apply GlobalTheory.KFiClose.kFi_of_tie <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_glint_nearAt {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : ℕ)
    (k : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hk : CongAt (seamP s P) 0 k) (hk' : CongAt (seamP s P) 0 k⁻¹) :
    ∃ g : GLint X.E n P, NearAt (seamP s P) d k (seamGL s g.1) := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.TwU.Approx.exists_nearAt D.host.F D.host.E n (d + 1) (seamP s P) k
  set h := seamLE s g0 with hhdef
  have hh : seamGL s h = g0 := seamGL_seamLE s g0
  have hC : CongAt (F := D.host.F) (seamP s P) (d + 1) (k⁻¹ * ratA D.host.F (seamGL s h)) := by
    rw [hh]; exact hg0
  have h0 : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h)) := by
    have e : ratA D.host.F (seamGL s h) = k * (k⁻¹ * ratA D.host.F (seamGL s h)) := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 hk (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _) hC)
  have h0' : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h⁻¹)) := by
    rw [map_inv, map_inv]
    have e : (ratA D.host.F (seamGL s h))⁻¹ = (k⁻¹ * ratA D.host.F (seamGL s h))⁻¹ * k⁻¹ := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _)
      (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ (Nat.succ_pos d) hC)) hk'
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h h0
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h⁻¹ h0'
  have hmem : h ∈ GLint X.E n P := by
    refine fun w => ⟨fun hw => ?_, fun hw => GlobalTheory.FrameMove.mem_of_local P 0 h l1 w hw⟩
    have := GlobalTheory.FrameMove.mem_of_local P 0 h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (h w) = w from h.symm_apply_apply w] at this
  refine ⟨⟨h, hmem⟩, ?_⟩
  show CongAt _ d (k⁻¹ * ratA D.host.F (seamGL s h))
  exact GlobalTheory.FrameMove.congAt_mono (Nat.le_succ d) hC

end GlobalTheory.FrameShift

namespace GlobalTheory.FrameShift

theorem exists_pt_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i p y k hk hy
  choose g hg using fun P : SB t μ => exists_glint_nearAt t.seam P.1 ((t.cst μ).D P) (k P) (hk P).1 (hk P).2
  obtain ⟨q, κ, hN, hf, hfr, hκ⟩ := GlobalTheory.CplPt.exists_pt_frames p g
  refine ⟨q, hN, hf, fun P => ?_⟩
  have base := GlobalTheory.CplPt.nearAt_mul_int _ (hy P) (hg P) (GlobalTheory.CplPt.seamGL_int t.seam (g P))
  rw [hfr P, map_mul]
  by_cases hP : P.1 ∈ t.Pr.vGs
  · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
    have hq := (GlobalTheory.ColPeriod.levelPrimes t.X t.Pr t.sel t.S (t.tup μ) hPin.fields.ok t.pr_ok hPin.sel P).1.2
    have e : ((κ P)⁻¹).1 = (g P).1 * ((g P)⁻¹ * (κ P)⁻¹).1 := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [e, map_mul, ← mul_assoc]
    refine GlobalTheory.CplPt.nearAt_mul _ base ?_
    rw [hD]
    exact GlobalTheory.CplPt.congAt_one_of_redGL t.seam hq ((g P)⁻¹ * (κ P)⁻¹) (hκ P).1
  · rw [(hκ P).2 hP]
    exact base

end GlobalTheory.FrameShift
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem ratPt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi β x x' p γ hγ hx hp
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹) (GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form D _ _ _ (hP.crd_orth i hi) hγ)
  have hmv : ∀ y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ratA D.host.F (A.crd i hi) * (ratA D.host.F γ * y) = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * y) := by
    intro y
    rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_right]
  let a' : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K)) := (g, 1, 1)
  refine ⟨a' • p, ?_, ?_, ?_⟩
  · have e1 : (a' • p).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
    rw [e1, GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage, hg, hp.lat, hx, latCo_rat _ _ _ hγ]
  · intro P
    have hb := hp.frame P
    rw [hx, hmv, mul_assoc (ratA D.host.F (seamGL t.seam g.1))]
    by_cases hPg : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hPg
      have e0 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = ((g, (1 : GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs))) • p.deco).1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      rw [hD, e0] at hb
      rw [hD, e1]
      exact GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one t.seam p.deco ⟨P.1, hPg⟩ g (mq_rowSG_unif (t.tup μ) hP.fields.ok t.pr_ok hP.sel P) _ hb
    · have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
        unfold frsF
        rw [dite_eq_right hPg, dite_eq_right hPg]
        show g.1 * p.fr _ * (((1 : GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) _)⁻¹).1 = _
        simp
      rw [e1, map_mul, nearAt_rat_mul]
      exact hb
  · intro P v h hv
    rw [hx, hmv]
    exact GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)

end GlobalTheory.TwRat
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartPointFrames_move_rationalIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
        (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P))) := by
  first | exact @GlobalTheory.RatFrame.frame_rat | exact GlobalTheory.RatFrame.frame_rat | (intros; apply GlobalTheory.RatFrame.frame_rat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  first | exact @GlobalTheory.FnlAway.fnl_eq | exact GlobalTheory.FnlAway.fnl_eq | (intros; apply GlobalTheory.FnlAway.fnl_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartPoint_mul_level_same_decoration : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P w, p₁.deco.1.f P w = p.deco.1.f P w) := by
  first | exact @GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco | exact GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco | (intros; apply GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  first | exact @GlobalTheory.TieUnr.mt_eq_one_of_intUnit | exact GlobalTheory.TieUnr.mt_eq_one_of_intUnit | (intros; apply GlobalTheory.TieUnr.mt_eq_one_of_intUnit <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N j)), w ∈ p.deco.1.at P.1 → w ∈ p₁.deco.1.at P.1 → p₁.deco.1.f P w = p.deco.1.f P w) := by
  first | exact @GlobalTheory.TwV.FnlAway.fnl_away | exact GlobalTheory.TwV.FnlAway.fnl_away | (intros; apply GlobalTheory.TwV.FnlAway.fnl_away <;> assumption)
end
