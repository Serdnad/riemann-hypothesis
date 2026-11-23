module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle789
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle252
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle270
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutationFullnessOfReads
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle926
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

noncomputable section

namespace GlobalTheory.RefPair



theorem thetaPair_of_hasThetaAt (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (D : D7) {μt : D.what₂.Tup} {j : ℕ}
    (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (X : RowMod D rep j) (μ η : HChar D.host.E)
    (hΘ : HasThetaAt D Mr X μ η) (σ : D.what₂.FT) (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W))
    (hS : NG.IsIrrRep Mr.wt.ρ S)
    (hPair : ∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F (D.what₂.thetaT μt j y) ≠ 0)
    (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hπ : IsLocS (n := D.R.nV) S s π) (hτ : IsLocS (rep σ).S s τ) (hU : GlobalTheory.SmGL.IsUnitarisable τ.ρ) :
    GlobalTheory.ThetaGL.ThetaPair (μ.loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w))) := by
  obtain ⟨Ω, _, _, ω, Λ, φ₀, hinv, hread, hloc⟩ := hΘ
  obtain ⟨f, hf, F, hF, hne⟩ := hPair
  have hFmem : Mr.real F ∈ NG.AFall D.host.E D.R.nV Mr.wt.ρ := by
    have : Mr.real F ∈ LinearMap.range Mr.real := LinearMap.mem_range_self _ _
    rw [Mr.real_range] at this
    exact this.1
  let Fp : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Λ φ₀ Fp yp ≠ 0 := by
    rw [← hread F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP μt j) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]
  have hμc : IsComp μ s.w (μ.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc μ s.w, fun _ => rfl⟩
  have hηc : IsComp η s.w (η.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc η s.w, fun _ => rfl⟩
  have hl := hloc s _ _ hμc hηc
  let ℓ0 : Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hl h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin

  have hFiso : (Fp : GAf D.host.E D.R.nV → Mr.wt.W) ∈ NG.isoTyp Mr.wt.ρ S := hF
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV Mr.wt S hS s π hπ c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1

  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := GlobalTheory.FinTypSpanLoc.main D.host.E D.R.r (rep σ) s τ hτ c hc hci
  let ℓ2 : ↥(rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add (f := _)])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1

  let T' : π.V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := T1.codRestrict _ hT1.1
  let T'' : τ.V →ₗ[ℂ] ↥X.C := (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) : GAf D.host.E D.R.nV → Mr.wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → Mr.wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a), hT2.1 _⟩ : ↥(rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Λ ∘ₗ ι).compl₂ T').compr₂ (GlobalTheory.PairReadPf.precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form _ D.R.r (D.R.r + D.R.t) _ _ (μ.loc s.w) τ.ρ
    (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)))
    ((hBZ _).1 (Fin D.R.r) _ _ τ.smooth τ.irr) hU (GlobalTheory.HeckeComp.smooth_loc μ s.w) b
    (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ' a c'
  obtain ⟨xh, hxh, exh⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  obtain ⟨xg, hxg, exg⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
  have back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)),
      Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A := by
    intro n A
    ext k l
    simp
  have eh : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) :
      GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)) = h := by rw [exh]; exact back _ h
  have eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g := by rw [exg]; exact back _ g
  subst eh eg
  have hω := hιeq xh xg hxh hxg Φ Φ' hΦ'
  have key := hinv xh xg (ι Φ) (T' a) (T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh)) a))
    (T'' c') (T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg)) c'))
    (hT'eq xh hxh a) (hT''eq xg hxg c')
  rw [hω] at key
  show Λ (ι Φ') (T' (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)) _ a)) (T'' (τ.ρ _ c')) =
    Λ (ι Φ) (T' a) (T'' c')
  rw [twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at key
  exact key

end GlobalTheory.RefPair

namespace GlobalTheory.RefPair

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin


end GlobalTheory.RefPair

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CommFullLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx Formalism.L2.Pj
  GlobalTheory.TwInputs GlobalTheory.CommFullAll
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct




section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) {S : RatDat D.ntw}
  (YS : NExpRealS Rl cG S) (H : NExpRealH Rl cG S YS)

theorem hL_comm_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host)
    (hsp : IsSplitPl D.host P) (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hi : ∃ i, P ∉ D.ntw.S0 i)
    (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hkr : k ≤ D.R.r)
    (g : S.G) (x : S.WL ((i' : ℕ) + 1)) :
    H.hL ((i' : ℕ) + 1) k P ((S.A ((i' : ℕ) + 1)).ρ g x) = (S.A ((i' : ℕ) + 1)).ρ g (H.hL ((i' : ℕ) + 1) k P x) := by
  obtain ⟨α, Rc, ha, hRc⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hR.lev hR.fam i' hso hkr
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData Rl.toRealDat i' P k α Rc := ⟨hso, hg, hkr, ha, hRc⟩
  let hL' : (Fin (Rl.nW i') → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (Rl.nW i') → D.what₂.LL) :=
    (YS.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (YS.fi i').e.symm.toLinearMap
  have hH : Formalism.L2.Pj.HeckeJ.IsHkJ (sg0 D A3.A) ((Rl.FW i').j (sg0 D A3.A)) (Rl.HW i' (sg0 D A3.A)).e
      (heckeOn (Rl.MW i' (sg0 D A3.A)) Rc)
      ((((Rl.C.mu0 i').val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) hL' := by
    intro y
    have h := hX.tie i' k P hsp hso hi h2 hkr α Rc ha hRc ((YS.fi i').e.symm y) rfl
    simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
    exact h
  have hc := GlobalTheory.HeckeSup.comm_rho_cl (hR.lev.βW i') hR.fam.Sb hR.models.HW hR.models.gW (sg0 D A3.A) hd
    (GlobalTheory.ExportPin.Model.j_injective Rl hU i' _) (hU i' (sg0 D A3.A)).2.2 hH ((YS.fi i').eG g)
  apply (YS.fi i').e.injective
  have h := LinearMap.congr_fun hc ((YS.fi i').e x)
  simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [(YS.fi i').rho, ← h, ← (YS.fi i').rho, LinearEquiv.symm_apply_apply]

theorem commAll_fullAll_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) : CommAll D ∧ FullAll D := by
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine ⟨?_, ?_⟩
  · intro i j hj b k P hk g x
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    obtain ⟨-, hkr, hsp, hS0⟩ := hk
    obtain ⟨-, -, -, -, hso, -, h2P, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i) Rl.Sb P (hS0c i) (hS02 i) (hS0b i) hsp hS0
    have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      rw [Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 0 h)
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 1 h)
    have hc := hL_comm_raw Rl F cG YS H hR hU hX i' k P hsp hso ⟨i, hS0⟩ h2P hg hkr
    refine (YS.eF i _ b h1 h2).injective ?_
    rw [YS.act, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, YS.act, map_smul,
      hkFR_act S i _ b (H.hL _) (H.hs _ h1 h2) k P (YS.rho _ h1 h2) (YS.chi _ h1 h2) hc]
  · intro i j hj b
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    have hF := iso_span (YS.fi i') (hI i').2.1.2
    have hB := Bsup_span S i ((i' : ℕ) + 1) b hF
    obtain ⟨c, hc0, -, hc2⟩ := YS.bsup i ((i' : ℕ) + 1) b h1 h2
    let e := YS.eF i ((i' : ℕ) + 1) b h1 h2
    have hc0' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c ≠ 0 := by
      intro h0
      apply hc0
      apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      rw [h0, map_zero]
    have hle : Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) ≤
        (Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b))).comap e.symm.toLinearMap := by
      refine Submodule.span_le.2 fun z hz => ?_
      have hm : c • e.symm z ∈ D.nexp.Bsup i ((i' : ℕ) + 1) b := hc2 _ (by simpa [e] using hz)
      have hm' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c • e.symm z ∈
          Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b)) := by
        rw [algebraMap_smul]
        exact Submodule.subset_span hm
      have := Submodule.smul_mem _ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c)⁻¹ hm'
      rw [inv_smul_smul₀ hc0'] at this
      exact this
    refine eq_top_iff.2 fun t _ => ?_
    have ht : e t ∈ Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) := by
      rw [hB]; exact Submodule.mem_top
    have := hle ht
    simpa using this

end Raw

end GlobalTheory.CommFullLayer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.HoweGen

theorem cvType_mem_of_stable : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (U : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ P ∈ U, ∀ P' : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → P' ∈ U) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → P ∈ U → P' ∈ U) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W), R.ioP i x w ∈ U) → ∀ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → ∀ w, φ w ∈ U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t U hstab hlie hio φ hφ w
  have hadd : ∀ a b : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t (a + b) = R.ptP i t a + R.ptP i t b := by
    intro a b; unfold RealDat.ptP; simp
  have hsmul : ∀ (c : ℂ) (a : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t (c • a) = c • R.ptP i t a := by
    intro c a; unfold RealDat.ptP; simp
  have hzero : R.ptP i t 0 = 0 := by simpa using hsmul 0 0
  let M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) :=
    { carrier := {ψ | (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) ∧ ∀ w, ψ w ∈ U}
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.add_apply, hadd, h₁ u hu w', h₂ u hu w', map_add (f := _)]
        · simp only [LinearMap.add_apply]; exact U.add_mem (h₁' w) (h₂' w)
      zero_mem' := by
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.zero_apply, hzero, map_zero]
        · simp only [LinearMap.zero_apply]; exact U.zero_mem
      smul_mem' := by
        rintro c ψ ⟨h₁, h₁'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.smul_apply, hsmul, h₁ u hu w', map_smul]
        · simp only [LinearMap.smul_apply]; exact U.smul_mem c (h₁' w) }
  have hioM : ∀ x, R.ioP i x ∈ M := fun x =>
    ⟨fun u hu w' => ((hG.core.thP.ioP i t).1 u hu x w').symm, fun w => hio x w⟩
  have hne : M ≠ ⊥ := by
    obtain ⟨v, w₀, -, -, hv⟩ := (hG.core.thP.ioP i t).2.2
    intro hM
    have h0 : R.ioP i (PiTensorProduct.tprod ℂ v) ∈ (⊥ : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)) := hM ▸ hioM _
    rw [Submodule.mem_bot] at h0
    apply GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
    rw [← hv, h0]
    rfl
  have hφM : φ ∈ M := GlobalTheory.T.howeDuality_compactPair_realPlaces_irreducible D G Pl0 T A Ks R F hG hF i t M (fun ψ hψ => hψ.1)
    (fun ψ hψ τ Y hY ψ' hd => ⟨GlobalTheory.T.fockPolynomial_lieDerivative_equivariant D G Pl0 T A Ks R F hG hF i t τ Y hY ψ ψ' hψ.1 hd,
      fun w => hlie τ Y hY (ψ w) (ψ' w) (fun z => hd w z) (hψ.2 w)⟩) hne φ hφ
  exact hφM.2 w

end GlobalTheory.HoweGen
end
