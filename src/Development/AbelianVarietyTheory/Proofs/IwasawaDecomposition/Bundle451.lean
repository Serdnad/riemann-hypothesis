module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle414
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle386
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle246
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductList
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Formalism.LocalToGlobal.Columns.Bundle039
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle435
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle436
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
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ChiDVal

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

section Gen

variable {L : Type} [Field L] [NumberField L]

theorem ideles_snd_mul (a b : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v = (a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v := rfl

theorem ideles_snd_inv_mul (a : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (a : AdeleRing (𝓞 L) L).2 v = 1 := by
  rw [← ideles_snd_mul, inv_mul_cancel]
  rfl

theorem ideles_finite (a : Ideles L) : {v : HeightOneSpectrum (𝓞 L) | ¬ Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1}.Finite := by
  have h1 := (a : AdeleRing (𝓞 L) L).2.2
  have h2 := ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2.2
  refine Filter.eventually_cofinite.1 ((h1.and h2).mono fun v hv => ?_)
  have e1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.1
  have e2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.2
  have e3 := congrArg Valued.v (ideles_snd_inv_mul a v)
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := e3.symm
    _ ≤ 1 * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := mul_le_mul_left e2 _
    _ = _ := one_mul _

theorem exists_unif_zpow (v : HeightOneSpectrum (𝓞 L)) (y : v.adicCompletion L) (hy : y ≠ 0) :
    ∃ n : ℤ, Valued.v (((atFin v (unif v)) ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = Valued.v y := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨-WithZero.log (Valued.v y), ?_⟩
  have hu : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log h0]

theorem ideles_values {Gp : Type} [CommGroup Gp] (f : Ideles L →* Gp)
    (hU : ∀ a : Ideles L, (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a = 1) (S : Subgroup Gp)
    (hS : ∀ v, f (localIdele L v (atFin v (unif v))) ∈ S) (a : Ideles L) : f a ∈ S := by
  classical
  have key : ∀ (T : Finset (HeightOneSpectrum (𝓞 L))) (a : Ideles L),
      (∀ v, v ∉ T → Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro a ha
      rw [hU a fun v => ha v (Finset.notMem_empty v)]
      exact S.one_mem
    | insert v0 T _ ih =>
      intro a ha
      have hy : (a : AdeleRing (𝓞 L) L).2 v0 ≠ 0 := by
        intro h0
        have := ideles_snd_inv_mul a v0
        rw [h0, mul_zero] at this
        exact zero_ne_one this
      obtain ⟨n, hn⟩ := exists_unif_zpow v0 _ hy
      have h1 : f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) ∈ S := by
        refine ih _ fun v hv => ?_
        rw [← map_inv, ideles_snd_mul]
        by_cases hvv : v = v0
        · subst hvv
          rw [localIdele_snd_self, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hn]
          exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 hy)
        · rw [(localIdele_isSupportedAt L v0 _).2 v hvv, mul_one]
          exact ha v fun h => (Finset.mem_insert.1 h).elim hvv hv
      have h2 : f a = f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) * f (localIdele L v0 (atFin v0 (unif v0))) ^ n := by
        rw [map_mul, map_inv, map_zpow (localIdele L v0), map_zpow f, inv_mul_cancel_right]
      rw [h2]
      exact S.mul_mem h1 (S.zpow_mem (hS v0) n)
  exact key (ideles_finite a).toFinset a fun v hv => by
    by_contra h
    exact hv ((ideles_finite a).mem_toFinset.2 h)

end Gen

def coeffUnits (D : D7) : Subgroup ℂˣ where
  carrier := {z | ∃ r : D.what₂.LL, D.what₂.embLL r = (z : ℂ)}
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [map_mul, hr, hs, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [map_inv₀, hr, Units.val_inv_eq_inv_val]⟩

theorem chiD_mem_of {D : D7} {C : CharFrame D} (T : DtTied D C) (hV : C.chiPsi.ValuesIn 0 D.what₂.embLL) :
    ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ) := by
  intro z
  obtain ⟨a, rfl⟩ := T.surj z
  refine ideles_values (D.chiD.comp T.eDt) (fun a ha => D.chiD_UO _ ((T.UO_eq _).2 ⟨a, ha, rfl⟩)) (coeffUnits D) (fun v => ?_) a
  obtain ⟨y, hy⟩ := hV v (C.isChi.unr v)
  refine ⟨y, ?_⟩
  rw [hy]
  show _ = ((D.chiD (T.eDt (localIdele D.host.E v (atFin v (unif v)))) : ℂˣ) : ℂ)
  rw [T.chiD_eq _ (fun w => (localIdele_isSupportedAt D.host.E v _).1 w)]
  unfold HChar.valTw
  rw [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rfl

theorem chiD_values_and_cc_top : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), (∀ z : (w.D Z).Dt, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r = (((w.D Z).chiD z : ℂˣ) : ℂ)) ∧ ∀ (L : SizeData₂ (w.D Z)) (hT : GatTies (w.D Z)) (Gi : G.Inst (w.D Z) L) (Gl : G.LatInst (w.D Z)) (K : G.Consts) (Y : DivX (w.D Z)) (cX : ExtraC) (ex : Extra (w.D Z) L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.cc = ⊤ := by
  intro B f T w Z
  refine ⟨?_, fun L hT Gi Gl K Y cX ex t => t.cc_rec.trans B.toPre.ccK_top⟩
  obtain ⟨dt, -⟩ := TC.dtTied_true w.I w.ok w.pins w.l Z
  have hv : Formalism.L2.Host.ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
    rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
    subst C_eq
    exact val _ _ _ _ _ _
  exact chiD_mem_of dt hv.toLL.chiPsi

end GlobalTheory.Mem.ChiDVal
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_of_matEq {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) (y : GL (Fin b) A)
    (hm : MatEq x y) : y = castGL h x := by
  subst h
  ext i j
  simp only [castGL, Units.coe_mapEquiv, MulEquiv.coe_toMonoidHom]
  simp [Matrix.reindexAlgEquiv_apply]
  exact (hm.2 i j i j rfl rfl).symm

theorem matEq_castGL {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) : MatEq x (castGL h x) := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  obtain rfl := Fin.ext hi
  obtain rfl := Fin.ext hj
  simp [castGL]

theorem castGL_mem_UA_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {a b : ℕ} (h : a = b) (x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.UA hc 1) :
    castGL h x ∈ Formalism.L2.DIV.UA hc 1 := by
  subst h
  have e : castGL (rfl : a = a) x = x := by
    ext i j
    simp [castGL]
  rwa [e]



theorem brgStdV_of_readsStd_one : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i hβ hgram c hc P hR hcoef
  unfold BrgStdV StdSide
  refine ⟨c, ?_, ?_, ?_, X.toD7.sp.cm, ?_⟩
  · intro γ γE g hr hm v
    have hg : g = castGL (rkEq X i).symm γE := castGL_of_matEq _ γE g hm
    subst hg
    exact hc γ γE hr v
  · intro hcm t φ h x hm
    refine ((hR t _ h).trans (hcoef t _)).trans ?_
    congr 1
    rw [Formalism.L2.Col.decoPt_mk]
    unfold ptL
    congr 1
    rw [hβ] at hm
    have hx := castGL_of_matEq (rkEq X i).symm _ _ hm
    rw [hx]
    simp only [matIn, mul_one, inv_one, one_mul, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  · have hli := (P (Formalism.L2.DIV.mu0F _)).coef_li
    simp only [hcoef] at hli
    exact hli
  · intro h
    obtain ⟨g, hg⟩ := h.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) h.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hg]; exact GlobalTheory.LevSplit.finE_mem_UA _ g
    rw [hgram] at h1
    refine ⟨⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1), castGL_mem_UA_std _ _ _ h1⟩, ?_⟩
    rw [hβ]
    have hm := matEq_castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1)
    simp only [matIn, mul_one]
    exact hm

end GlobalTheory.Mem.R3.LiftBrg
end

section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

section Core

variable {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
  (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)
  (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y))



def sIsoRe (hR : Formalism.L2.Theta.RealTied D) (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) :
    SIso (reD D ⟨P.toNew hD j, N, hh⟩).s (sOf hF) where
  cd := by
    have h := (real_reS D (P.toNew hD j)).1 hR
    exact cdScale_eq_cdScaleOf (reD D ⟨P.toNew hD j, N, hh⟩) ((by with_unfolding_all exact (h.cdScale :)))
  del := rfl
  letter := rfl
  eHH := (by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))
  eCu := fun u => (by with_unfolding_all exact (eCure ⟨P.toNew hD j, N, hh⟩ P.fin hF u :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).1 :))
  volN := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).1 :))
  volH := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).2 :))
  eT := fun u u' => (by with_unfolding_all exact (eRT ⟨P.toNew hD j, N, hh⟩ P.Y u u' :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => by
    apply Subtype.ext
    exact (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.1 :))
  atP := fun p => (by with_unfolding_all exact ((hL p).some :))
  ePl := (by with_unfolding_all exact (Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.1 q :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.1 :))
  eP := fun u u' => (by with_unfolding_all exact ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose :))
  pfst := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1 :))
  psnd := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.1 :))
  s0 := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.1 :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.1 :))
  pval := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.2 :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} (p : RP P.Y u u') => by
    have h1 := ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 p.1.1).2.2.2.2.2.2.2.2.1
    have h2 := ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1
    exact (by with_unfolding_all exact (h1.trans (congrArg (fun t => Formalism.L2.SG.PairVal.massTerm t) h2) :))
  meanCount := by
    funext u u' w
    exact (by with_unfolding_all exact ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').2 w :))

end Core

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe



theorem exists_sRest_re : ∀ (D : D7) (F : ∀ u, Forms0 D u) (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F F') (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)), Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.Theta.RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → ∃ S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro D F P hD j N hh F' hs hF hph hL hR hDs
  have hR' := (real_reS D (P.toNew hD j)).1 hR
  have hDs' : (reD D ⟨P.toNew hD j, N, hh⟩).what₂.Dstar = StandardLattice.DstarD (reD D ⟨P.toNew hD j, N, hh⟩) := (by with_unfolding_all exact (hDs.trans (real_reS D (P.toNew hD j)).2.1.symm :))
  have hAut : Formalism.MainNotions.S.AutTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.B
      (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.pl :=
    GlobalTheory.BundleTie.autTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X
      ⟨(by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))⟩ ((by with_unfolding_all exact (hph :))) hDs' (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).inst
      ((by with_unfolding_all exact (Formalism.L2.Theta.VolTieG.volTie hR'.vol :))) ((by with_unfolding_all exact (hR'.cdScale :))) ((by with_unfolding_all exact (hR'.dsig_all :)))
  refine ⟨⟨sIsoRe P hD j N hh hF hR hL, hAut, ?_, j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G), ?_, (by with_unfolding_all exact (hL :))⟩, rfl⟩
  · intro u x
    apply Subtype.ext
    exact (by with_unfolding_all exact (colDictL_reTr ⟨P.toNew hD j, N, hh⟩ (P.tr u) (hs u).2.1 (hs u).2.2 P.Y.hK x :))
  · intro x
    exact (by with_unfolding_all exact ((conjHH_eEECre ⟨P.toNew hD j, N, hh⟩ P.G (j x)).symm :))

end GlobalTheory.Mem.SRe
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.classSums_eq_pairings_topChain_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  first | exact @GlobalTheory.TopNorm.classSums_topNorm | exact GlobalTheory.TopNorm.classSums_topNorm | (intros; apply GlobalTheory.TopNorm.classSums_topNorm <;> assumption)
end

section

open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.HCChar

open Formalism.IrreducibleCountingLemmas.TYPES

theorem trace_hcRep_eq_hcL : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b →
    ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
      (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x := by
  intro g _ r s b lam _ x
  classical
  have h1 : LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x) =
      (Representation.coind (parab (ZMod g) b).subtype (PI.SerBridgeGLW.inflRep (ZMod g) b lam)).character x := rfl
  rw [h1, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let α : ∀ c, GlobalTheory.GLq.Gn g (d c) → ℂ := fun c y => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character y
  let j : ∀ c, Fin (d c) → Fin r := fun c t => ((Fintype.equivFin {i // b i = c}).symm t).1
  obtain ⟨σ, hσ1, -, hσ3, hσ4⟩ := GlobalTheory.TypeCharProduct.exists_enum b d α j
    (fun c => Subtype.val_injective.comp (Equiv.injective _))
    (fun c t => ((Fintype.equivFin {i // b i = c}).symm t).2)
    (fun i => ⟨Fintype.equivFin {k // b k = b i} ⟨i, rfl⟩, by simp [j]⟩)
    (List.finRange s) (List.pairwise_lt_finRange s)
  have hL : GlobalTheory.SerCmp.canonList b lam = (List.finRange s).map fun c => (⟨d c, α c⟩ : GlobalTheory.GLq.Pc g) := rfl
  rw [hL, ← GlobalTheory.TypeCharProduct.ind_eq_hcL _ ?_ r σ ⟨hσ1, fun i => hσ3 i (List.mem_finRange _)⟩
    (fun y => y ∈ parab (ZMod g) b)
    (fun y => if h : y ∈ parab (ZMod g) b then (PI.SerBridgeGLW.inflRep (ZMod g) b lam).character ⟨y, h⟩ else 0)
    ?_ ?_]
  · unfold GlobalTheory.BI.ind GlobalTheory.TypeCharProduct.ind
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold GlobalTheory.BI.ext0
    beta_reduce
    by_cases h : y⁻¹ * x * y ∈ parab (ZMod g) b
    · rw [dite_eq_left h, if_pos h]
    · rw [dite_eq_right h, if_neg h]
  · intro q hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    intro y z
    exact FDRep.char_conj _ y z
  · intro y
    rw [(hσ4 _).1, GlobalTheory.HCInduction.parab_eq_blockTri]
    show Matrix.BlockTriangular _ _ ↔ _
    simp only [List.mem_finRange, true_implies]
    exact ⟨fun h i k hik => h hik, fun h i k hik => h i k hik⟩
  · intro y hy
    rw [dite_eq_left hy, (hσ4 _).2, ← Fin.prod_univ_def]
    show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi (ZMod g) b c ⟨y, hy⟩)) = _
    rw [PI.SerBridgeGLW.trace_piTensorMap]
    refine Finset.prod_congr rfl fun c _ => ?_
    have hu : (y : Matrix (Fin r) (Fin r) (ZMod g)).submatrix (j c) (j c) =
        ((glEquiv (ZMod g) (Fintype.equivFin {i // b i = c}) (levi (ZMod g) b c ⟨y, hy⟩) : GL _ (ZMod g)) :
          Matrix _ _ (ZMod g)) := by
      ext t t'
      simp [glEquiv, levi, blk, j, Matrix.reindexAlgEquiv]
    have hg : GlobalTheory.GLq.toG ((y : Matrix (Fin r) (Fin r) (ZMod g)).submatrix (j c) (j c)) =
        glEquiv (ZMod g) (Fintype.equivFin {i // b i = c}) (levi (ZMod g) b c ⟨y, hy⟩) := by
      apply Units.ext
      rw [GlobalTheory.TypeCharProduct.coe_toG (by rw [hu]; exact Units.isUnit _), hu]
    show _ = (transp (Fintype.equivFin {i // b i = c}) (lam c)).character _
    rw [hg]
    show _ = LinearMap.trace ℂ _ ((lam c).ρ ((glEquiv (ZMod g) (Fintype.equivFin {i // b i = c})).symm _))
    rw [MulEquiv.symm_apply_apply]

end GlobalTheory.HCChar
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_framed_chart_from_adelic_dictionary : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E hc.sig J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (e : ℕ) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (k t : GL (Fin n) (AfE F E)) (C : Type) (s : C → DecoF E n ST SG Q) (y : C → GL (Fin n) (AfE F E)) (stab : C → Type) [∀ c, Group (stab c)] (lat : C → Submodule (𝓞 E) (Fin n → E)) (gm : ∀ c, stab c →* UF E n) (ψ : topU S.U t Θ d →* ℂˣ), J = 1 → (∀ v, v ∈ Qv ↔ ∃ P ∈ Q, P.under (𝓞 F) = v) → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → (∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) → k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ S.U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → (∀ c, IsPtOf hc (y c * (k * t)) (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → (∀ c, lat c = (s c).deco.1.L) → (∀ c, Function.Injective (gm c)) → (∀ c (γ : UF E n), γ ∈ (gm c).range ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c) → (∀ x : topU S.U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → ψ x = 1) → ∃ C' : ClsG hc.sig J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) stab lat, C'.lev.Lb = S.Lb ∧ C'.lev.U = topU S.U t Θ d ∧ (∀ v, v ∉ Qv → C'.lev.Uloc v = S.Uloc v) ∧ (∀ (x : C'.lev.U) (x' : S.U) (x'' : topU S.U t Θ d), x.1 = x'.1 → x.1 = x''.1 → C'.lev.chi x = S.chi x' * ψ x'') ∧ (∀ c, (C'.y c).1 = y c) ∧ ∀ c s, (C'.stabI c s).1 = ufGL E n (gm c s) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | exact GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | (intros; apply GlobalTheory.Mem.Col2.TopCh.exists_clsG_top <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tupleChain_complexForms_eq_algebraicModularForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  first | exact @GlobalTheory.Mem.Col2.TwP.ptC_tw | exact GlobalTheory.Mem.Col2.TwP.ptC_tw | (intros; apply GlobalTheory.Mem.Col2.TwP.ptC_tw <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tupleChain_forms_rational_iff_frame_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ z : (I.per l u a).Wrow, (∃ x, (I.fm l u a).ptEmb x = z) ↔ z ∈ (I.fm l u a).ptC ∧ ∀ c, ∃ Pc ∈ RatSpan (I.rec7 l Z) (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) 1 Pc := by
  exact @GlobalTheory.Mem.Col2.TwP.ptEmb_iff_rat
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev


theorem _root_.GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E}, J = 1 →
    ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ),
    (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → (∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') →
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      ∀ᶠ (u : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) →
    RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ →
    RdLevOn hc Set.univ S.U S.chi Λ emb Q HQ lamQ := by
  first | exact @GlobalTheory.SeeSaw.TwLev.Approx.rd_all | exact GlobalTheory.SeeSaw.TwLev.Approx.rd_all | (intros; apply GlobalTheory.SeeSaw.TwLev.Approx.rd_all <;> assumption)
end
