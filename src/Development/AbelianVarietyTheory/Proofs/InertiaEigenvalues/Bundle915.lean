module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle905
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle904
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle903
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle798
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle907
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.BaseClassSum

variable {D : D7} {S T : HSp D}

theorem series_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω : PairRep S T} (hω : B.IsWeil t.chi ω) {h h' : GA D S} (hh : h ∈ GfC S) (hh' : h' ∈ GfC S) (γ : GQ S) (k : B.levJ t)
    (e : finPt S h = Bridge.ratF S γ * finPt S h' * (k : Bridge.Gf S)) (P : PolF D T.rank S.rank) :
    series B.F ω (B.vecFlat t) h P =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • series B.F ω (B.vecFlat t) h' (B.act ((γ⁻¹ : GQ S) : GA D S) P) := by
  obtain ⟨hsplit, hcomm, htriv, -, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨x, hx⟩ := (k : Bridge.Gf S).2
  obtain ⟨kk, hkk, -, -, -, hfk⟩ := GlobalTheory.LiftUnfold.exists_fin_mul_real S x
  have hkk' : finPt S kk = (k : Bridge.Gf S) := hfk.trans (Subtype.ext hx)
  obtain ⟨ga, hga, gf, hgf, hγ⟩ := hsplit (γ : GA D S)
  have hfγ : Bridge.ratF S γ = finPt S gf := by
    change finPt S (γ : GA D S) = _
    rw [hγ]
    dsimp only [finPt]
    rw [map_mul]
    have : (finHom S).rangeRestrict ga = 1 := Subtype.ext (MonoidHom.mem_ker.1 hga)
    rw [this, one_mul]
  have eh : h = (γ : GA D S) * h' * ga⁻¹ * kk := by
    have eg : gf = (γ : GA D S) * ga⁻¹ := by
      rw [hγ, hcomm ga hga gf hgf, mul_inv_cancel_right]
    have e1 : h = gf * h' * kk := by
      set y := (gf * h' * kk)⁻¹ * h with hy
      have hyf : y ∈ GfC S := mul_mem (inv_mem (mul_mem (mul_mem hgf hh') hkk)) hh
      have hyi : y ∈ GinfC S := by
        have : finPt S y = 1 := by
          rw [hy]
          dsimp only [finPt] at hkk' hfγ e ⊢
          rw [map_mul, map_inv, map_mul, map_mul, hkk', ← hfγ]
          change _ * ((finHom S).rangeRestrict h) = 1
          rw [e]
          exact inv_mul_cancel _
        exact MonoidHom.mem_ker.2 (congrArg Subtype.val this)
      have := htriv y hyi hyf
      rw [hy, inv_mul_eq_one] at this
      exact this.symm
    rw [e1, eg, mul_assoc (γ : GA D S) ga⁻¹ h', hcomm ga⁻¹ (inv_mem hga) h' hh', ← mul_assoc]
  have hact : B.act ((γ⁻¹ : GQ S) : GA D S) = B.act ga⁻¹ := by
    have hr : GlobalTheory.ExportSeries.realGL B.F.θ S gf = 1 := by
      funext τ
      show Formalism.UG.bc (B.F.θ τ) (infHom S gf) = 1
      rw [MonoidHom.mem_ker.1 hgf, map_one]
    rw [Base.act, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_inv, hγ, _root_.mul_inv_rev, map_mul, map_inv _ gf, hr,
      inv_one, one_mul]
  have hJ : finPt S kk ∈ B.levJ t := hkk' ▸ k.2
  have hθf : ∀ P, IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) P) := Base.isThetaFunO_fock_vecAt hB hQ _
  have hk : ω (kk, 1) (B.F.fock (B.vecFlat t) P) = ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) P := by
    have h1 := GlobalTheory.ExportSeries.DualType.dual_type_fock hB hS ht hQ hω hkk hJ P
    have e2 : ((B.levLam t ⟨_, hJ⟩ : ℂˣ) : ℂ) = ((B.levLam t k : ℂˣ) : ℂ) :=
      congrArg (fun z : B.levJ t => ((B.levLam t z : ℂˣ) : ℂ)) (Subtype.ext hkk')
    rw [← e2]
    exact h1
  have ha : ω (ga⁻¹, 1) (B.F.fock (B.vecFlat t) P) = B.F.fock (B.vecFlat t) (B.act ga⁻¹ P) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ω t.Q _ hB ht hQ hω ga⁻¹ (inv_mem hga) P
  have ep : ∀ g : GA D T, (((γ : GA D S) * h' * ga⁻¹ * kk, g) : GA D S × GA D T) =
      ((γ : GA D S), 1) * ((h', g) * ((ga⁻¹, 1) * (kk, 1))) := fun g => by
    ext <;> simp [mul_assoc]
  have key : ∀ g : GA D T, ω (h, g) (B.F.fock (B.vecFlat t) P) 0 =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ * ω (h', g) (B.F.fock (B.vecFlat t) (B.act ga⁻¹ P)) 0 := fun g => by
    rw [eh, ep g, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hk, map_smul, ha,
      map_smul, map_smul, Pi.smul_apply, hω.om_aut _ γ.2 1 (one_mem _) _ (hω.om_pres _ _ (hθf _)), smul_eq_mul]
  refine funext fun g => ?_
  rw [Pi.smul_apply, smul_eq_mul, hact]
  exact key g

theorem series_triv (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h P = ρ.theta i j b h P := by
  have key : ∀ t : Twist D Circle, t.Q = ∅ → t.chi = 1 →
      series (ρ.B i j b).F (ρ.om i j b t.chi) ((ρ.B i j b).vecFlat t) h P = ρ.theta i j b h P := by
    rintro ⟨_, _, r⟩ rfl rfl
    show series _ _ ((ρ.B i j b).vecAt ∅ _) h P = series _ _ (ρ.B i j b).vecBase h P
    rw [Base.vecAt_empty]
  exact key _ (half_empty _) (charOf_one _ _)

theorem term_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank} (hF : F ∈ (ρ.B i j b).formsC (ρ.tw i b 0 ∅ 1))
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h (F (finPt _ h)) ∈
      Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hB := hρ.base i j b
  have hω := hρ.weil i j b _ hg
  obtain ⟨γ, s, h', k, hs, hoff, hh', hsupp, e⟩ := GlobalTheory.RankReps.exists_rep_split_levJ D ρ hρ i j b h hh
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF).2 γ (finPt _ h') k
  have hval : F (finPt _ h') ∈ (ρ.B i j b).valSpace := ((ρ.B i j b).mem_formsC.1 hF).1 _
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e, hlaw, LinearMap.map_smul, series_move hB (D.sp.V_sig _) hg ha hω hh hh' γ k e, hinv, smul_smul,
    mul_inv_cancel₀ (Units.ne_zero _), one_smul, series_triv]

  have hspan : F (finPt _ h') ∈ Submodule.span ℂ (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have h2 := (GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D (Wc D j).rank (Vc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS _ (Formalism.L2.Host.embLL0 D) (labLL0 D)
      (ρ.eO i b).range ((ρ.B i j b).latAt (finPt _ h')) hB.wt hm (hρ.isCoefRing i b)
      (GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b h')).2
    have h3 : (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) =
        (harmLat (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.eO i b).range (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS
          ((ρ.B i j b).latAt (finPt _ h')) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := rfl
    rw [h3, h2]
    exact hval
  have hmap := Submodule.mem_map_of_mem (f := (ρ.B i j b).theta (ρ.om i j b 1) h') hspan
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨s, h', P, ⟨hs, hoff, hh', hsupp, hP⟩, rfl⟩

theorem sum_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank}
    (hF : F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))) :
    ρ.sum i j b 0 ∅ 1 F ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hc := hρ.classes i j b _ hg ha
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hF' := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
    rw [Setup.sum, Base.classSum_apply]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (term_mem_span hρ i j b hF'.1 (hc.fin c))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BaseClassSum

namespace GlobalTheory.TwInputs

theorem spanGood_of_sumOnto : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  intro D ρ hρ rd i hS j b x hx
  obtain ⟨F, hF, e⟩ := hS j b x hx
  rw [e]
  exact GlobalTheory.BaseClassSum.sum_mem_span hρ i j b hF

end GlobalTheory.TwInputs
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceHeckeCommute_of_twistSeriesSideData : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), HkComm D := by
  first | exact @GlobalTheory.SupLaw.hkComm_of_ties | exact GlobalTheory.SupLaw.hkComm_of_ties | (intros; apply GlobalTheory.SupLaw.hkComm_of_ties <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_low (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (j : Fin D.R.m) :
    ∃ u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ, (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) := by
  have h := (Y.Z.vec j).1
  exact ⟨fun ρ => ⟨X.geo.v₀ j _ ρ, (h ρ).2.1⟩, rfl⟩


open Classical in
theorem sum_eq_classSum_ωP (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (t : X.T) (hxi : X.R.xi t = (Y.Z.ρ.B i j b).de.chi) (hQ : X.R.Q t = (Y.Z.ρ.B i j b).de.Q) :
    Y.Z.ρ.sum i j b 0 ∅ 1 = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) := by
  have hB : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact
      ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have h1 : IsWeilDatumO X.R.toRealDat.ψ (Vc D j) (Wc D j) (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).2 (Y.Z.ρ.om i j b 1) := by
    have := Y.Z.good.weil_base i j b
    rw [Base.IsWeil, show (1 : (AE D)ˣ →* Circle) = (Twist.triv Circle ∅ : Twist D Circle).chi from rfl,
      hB.mu_mul htup, hB.ψ, hB.eta] at this
    exact this
  have hu := (GlobalTheory.SplitChange.change_of_splitting D X.R.toRealDat.ψ (Vc D j) (Wc D j) (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta (Y.Z.ρ.B i j b).mu0
    ((j : ℕ) + 1) (X.R.ωP j t) (X.char.thP.ωP j t) hG.hecke hG.real).2.2 _ h1
  have key : ∀ τ : Twist D Circle, τ.Q = ∅ → τ.chi = 1 → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      series (Y.Z.ρ.B i j b).F (Y.Z.ρ.om i j b τ.chi) ((Y.Z.ρ.B i j b).vecFlat τ) h P =
        series (Y.Z.ρ.B i j b).F (X.R.ωP j t) ((Y.Z.ρ.B i j b).vecFlat τ) h P := by
    rintro ⟨Q0, c0, r0⟩ hq hc h P
    dsimp only at hq hc
    subst hq hc
    funext g
    rw [series_apply, series_apply]
    have ht := Base.isThetaFunO_fock_vecAt hG (Base.admissible_empty_of_good hG) (fun _ _ => (1 : ℂ)) P
    rw [hB.ψ] at ht
    exact congrFun (hu (h, g) _ ht) 0
  apply LinearMap.ext
  intro F
  rw [Setup.sum, Base.classSum_apply, Base.classSum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [key _ (half_empty _) (charOf_one _ _)]

end GlobalTheory.LiftClassSum

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.good_type_form_reading_right_translate_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  first | exact @GlobalTheory.TypeRead.rd_mul_lift | exact GlobalTheory.TypeRead.rd_mul_lift | (intros; apply GlobalTheory.TypeRead.rd_mul_lift <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.L2.Host (embLL0)
open scoped TensorProduct




namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Export

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)


variable {YS v₀ i j b} in
theorem mem_range_realRd_of_sum {ν : ℂ} (hν : ν ≠ 0) {g : GA D (Wc D j) → ℂ} {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ k, ∃ y, ρ.e i b y = z k) (x : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h : ν • g = ∑ k, z k • evW YS v₀ j (Subtype.val (x k))) : g ∈ Set.range (realRd YS v₀ hρ i j b ν) := by
  choose y hy using hz
  exact (mem_range_realRd_iff YS v₀ hρ i j b hν g).2 ⟨n, y, x, h.trans (Finset.sum_congr rfl fun k _ => by rw [← hy k])⟩


variable (ρ) in
def UnrComb (Φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (k L : Type) (_ : Field k) (_ : NumberField k) (_ : Field L) (_ : NumberField L) (_ : Algebra k L)
    (ι : k →+* FractionRing (D.ntw.O i)) (σ : L →+* ℂ), Normal k L ∧
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime], ((D.ntw.l i : ℕ) : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 k) P) ∧
    (∀ a, σ (algebraMap k L a) = ρ.e i b (ι a)) ∧
    ∃ (n : ℕ) (a : Fin n → L) (x : Fin n → NX.FmK S ((j : ℕ) + 1)), Φ = ∑ c, σ (a c) • evW YS v₀ j (Subtype.val (x c))


variable {YS v₀ i j b}

end Export

section Any

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}


variable (ρ Y i j b) in
def xiLin (Q : Finset (Pl D.host.E)) (M : ℕ) (h : GA D (Vc D j)) (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ) where
  toFun P := ρ.xi i j b Y Q M h P a
  map_add' P P' := by funext g; simp only [Base.xiCoef_apply, map_add (f := _), Pi.add_apply]
  map_smul' c P := by funext g; simp only [Base.xiCoef_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem Faithful.mem_range_of_smul {rd : Rd ρ Y i j b} (hF : Faithful rd) {g : GA D (Wc D j) → ℂ} (hg : g ≠ 0) {u : ℂ}
    (h1 : g ∈ Set.range rd) (h2 : u • g ∈ Set.range rd) : ∃ y, ρ.e i b y = u := by
  obtain ⟨f, rfl⟩ := h1
  obtain ⟨f', h2⟩ := h2
  have hf : f ≠ 0 := fun h => hg (by rw [h, map_zero])
  have hdep : ¬ LinearIndependent (FractionRing (X.O i)) ![f, f'] := fun h => by
    have h3 : LinearIndependent ℂ ![rd f, rd f'] := by
      convert hF 2 _ h using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h3 u (-1) (by rw [h2]; simp)).2
    simp at this
  rw [LinearIndependent.pair_iff' hf] at hdep
  push Not at hdep
  obtain ⟨y, rfl⟩ := hdep
  rw [map_smulₛₗ] at h2
  exact ⟨y, smul_left_injective ℂ hg h2⟩

theorem mem_range_of_small (rd : Rd ρ Y i j b) (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → Φ P ∈ Set.range rd)
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) :
    Φ P ∈ Set.range rd := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ Φ P' ∈ Set.range rd := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, 0, by rw [map_zero, map_zero]⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂, e2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, f₁ + f₂, by rw [map_add (f := _), map_add (f := _), e1, e2]⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, o • f₁, by rw [rd_smul, map_smul, e1]⟩
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Any

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

variable {YS v₀ i j b}

end Main

section Core
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem exists_evW_eq_phiC (t : FWTie T Rl.toRealDat κ v₀) (ht : t.Evaluates) (j : Fin D.R.m)
    (hσ : GoodEmb T.Q.c (res T (sg0 D A3.A))) (hV : T.V ((j : ℕ) + 1) (res T (sg0 D A3.A)) = Wc D j) (f : Cu T κ j) :
    ∃ x : NX.FmK S ((j : ℕ) + 1), evW YS v₀ j (Subtype.val x) = phiC T hV (wtA (κ j)) (f : T.R ((j : ℕ) + 1)) := by
  have hx : (YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) ∈ (S.A ((j : ℕ) + 1)).WK := by
    refine ((YS.fi j).wk _).2 ?_
    have e1 : (YS.fi j).e ((YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)) =
        ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) := LinearEquiv.apply_symm_apply _ _
    rw [e1]
    exact (t.e j f).2
  refine ⟨⟨_, hx⟩, Eq.trans ?_ (ht j (sg0 D A3.A) hσ hV f)⟩
  have e2 := LinearEquiv.apply_symm_apply (YS.fi j).e ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [e2]
  rfl

end Core
end GlobalTheory.SeriesTie
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



theorem _root_.GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (V : HSp D) (P : Pl D.host.E) (k : ℕ) (α : GA D V) (z : (AE D)ˣ), ChrEq c χ → GlobalTheory.ExportSeries.UnramOutside c Q → GlobalTheory.ExportSeries.SplitSet Q → Bridge.SplitOff P (Q : Set (Pl D.host.E)) → IsHeckeAt V P k α → IsDetAt (idemAt P) V α z → ((c z : Circle) : ℂ) = ((χ.val P : ℂˣ) : ℂ) ^ k := by
  first | exact @GlobalTheory.HeckeDetValue.chr_detAt | exact GlobalTheory.HeckeDetValue.chr_detAt | (intros; apply GlobalTheory.HeckeDetValue.chr_detAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

theorem isExtremalVector_of_realSideBaseChange : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι), (∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) →
    ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _) := by
  intro D D' ι e h X X' m _ j
  exact X'.geo.fw.hv₀ j _

end GlobalTheory.TwInputs.Move
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie

theorem _root_.GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace : ∀ (D : D7) (T0 : CoreJ D), LawsJ T0 → ∀ (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host), Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime T0.Q.H T0.Q.l P.asIdeal (charAt P) ∧ charAt P ≠ D.ntw.l i := by
  first | exact @GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx | exact GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx | (intros; apply GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx <;> assumption)
end
