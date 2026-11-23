module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensitySumsAndDomination
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem act_mul (f : Fin (D.R.rS + 1) → (VS D).V) (s s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A B : MatR D)
    (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (hs' : ∀ b, s' (f b) = ∑ c, B c b • f c) (b : Fin (D.R.rS + 1)) :
    (s * s') (f b) = ∑ c, (A * B) c b • f c := by
  show s (s' (f b)) = _

  rw [hs', map_sum]
  simp only [map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem act_inv' (f : Fin (D.R.rS + 1) → (VS D).V) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : MatR D)
    (hA : IsUpUni A) (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (b : Fin (D.R.rS + 1)) :
    s⁻¹ (f b) = ∑ c, A⁻¹ c b • f c := by
  apply s.injective
  show s (s.symm (f b)) = _
  rw [LinearEquiv.apply_symm_apply, Formalism.L2.SG.Pf.ZsVolKey.act_inv f s A (Formalism.L2.SG.Pf.ZsVolKey.up_inv_mul hA) hs b]

theorem act_one (f : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f b) = ∑ c, (1 : MatR D) c b • f c := by
  simp [Matrix.one_apply]

theorem nlam_one {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨(Formalism.L2.SG.Pf.isAutLam_iff Λ 1).2 ⟨fun x y => rfl, fun x => Iff.rfl⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

variable (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def stabAutG (t : Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) : Subgroup (GLR D) where
  carrier := stabAutSet D u u' F0 what₂ t F' L
  one_mem' := by
    refine ⟨1, ⟨nlam_one _ _, nlam_one _ _⟩, 1, act_one _, ?_⟩
    rw [Units.val_one, Matrix.conjTranspose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)]
  mul_mem' := by
    rintro x y ⟨s₁, ⟨h1F, h1F'⟩, uu₁, hu₁, hx⟩ ⟨s₂, ⟨h2F, h2F'⟩, uu₂, hu₂, hy⟩
    refine ⟨s₂ * s₁, ⟨Formalism.L2.SG.Pf.nlamPf_mul h2F h1F, Formalism.L2.SG.Pf.nlamPf_mul h2F' h1F'⟩, uu₂ * uu₁,
      act_mul _ _ _ _ _ hu₂ hu₁, ?_⟩
    have hLL : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)
    rw [Units.val_mul, hx, hy, Matrix.conjTranspose_mul]
    calc L⁻¹ * uu₁.conjTranspose * L * (L⁻¹ * uu₂.conjTranspose * L) =
        L⁻¹ * uu₁.conjTranspose * (L * L⁻¹) * uu₂.conjTranspose * L := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨s, ⟨hF, hF'⟩, uu, hu, hx⟩

    obtain ⟨⟨⟨hiso, _⟩, hf1, hf2⟩, _⟩ := And.intro hF hF'
    obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
    have heq : uu = uu0 :=
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 hu hu0
    subst heq
    refine ⟨s⁻¹, ⟨Formalism.L2.SG.Pf.nlamPf_inv hF, Formalism.L2.SG.Pf.nlamPf_inv hF'⟩, uu⁻¹, act_inv' _ _ _ huu0 hu, ?_⟩
    have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
    have hUd : IsUnit uu.conjTranspose.det := by
      rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
    rw [Matrix.coe_units_inv, hx, Matrix.conjTranspose_nonsing_inv]
    refine Matrix.inv_eq_left_inv ?_
    calc L⁻¹ * (uu.conjTranspose)⁻¹ * L * (L⁻¹ * uu.conjTranspose * L) =
        L⁻¹ * ((uu.conjTranspose)⁻¹ * (L * L⁻¹) * uu.conjTranspose) * L := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ hLd, Matrix.mul_one, Matrix.nonsing_inv_mul _ hUd, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hLd]

theorem mem_stabAut_iff (t : Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) (a : GLR D) :
    a ∈ stabAut D u u' F0 what₂ t F' L ↔ a ∈ stabAutSet D u u' F0 what₂ t F' L := by
  have e : stabAut D u u' F0 what₂ t F' L = stabAutG u u' F0 what₂ t F' L hL hT0 :=
    Subgroup.closure_eq (stabAutG u u' F0 what₂ t F' L hL hT0)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolFib

end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.DataInst

variable {D : D7} (X : HidaSetting D)

theorem alX_eq (hEta : EtaTie X) (u u' : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    alX X u u' v = alpD u u' (plEquiv X v) := by
  have haP : ∀ T : ℕ, aP (E := X.B.I.E) v D.R.k X.B.I.n T = aPD (plEquiv X v) T := by
    intro T
    unfold aP aPD
    have hI : Finset.Icc (if ((T : 𝓞 X.B.I.F) ∈ v.asIdeal) then D.R.k else D.R.k + 1) X.B.I.n =
        Finset.Icc (if ((T : 𝓞 D.host.F) ∈ (plEquiv X v).asIdeal) then D.R.k else D.R.k + 1) D.R.r := by
      rw [X.n_eq]
      by_cases hm : ((T : 𝓞 X.B.I.F) ∈ v.asIdeal)
      · rw [if_pos hm, if_pos ((natCast_mem_plEquiv X v T).2 hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((natCast_mem_plEquiv X v T).1 h))]
    rw [hI]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hEta v, absNorm_plEquiv]
  unfold alX alpD Tw
  rw [haP, haP]
  by_cases h : TypAt X v
  · rw [if_pos h, if_pos ((typAt_iff X v).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((typAt_iff X v).2 h'))]

theorem summable_log_alpD (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    (∀ p, 0 < alpD u u' p) ∧ Summable fun p => Real.log (alpD u u' p) := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  have hα := Formalism.L2.SG.IntegralApproximation.AlpBound_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := hα hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  refine ⟨hal0, ?_⟩
  refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
  have h2 := Real.log_le_log (hal0 p) (hαb p).2
  rw [Real.log_exp] at h1 h2
  have ha' : a p = (Formalism.L2.SG.DataCut.qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ := rfl
  constructor <;> linarith

theorem prod_split {β : Type} (f : β → ℝ) (s : Finset β) (hpos : ∀ v, 0 < f v)
    (hlog : Summable fun v => Real.log (f v)) :
    (∏ p : ↥s, f p.1) * ∏' v : {v // v ∉ s}, f v.1 = ∏' v, f v := by
  have hls : Summable (fun v : {v // v ∉ s} => Real.log (f v.1)) :=
    hlog.comp_injective (i := fun v : {v // v ∉ s} => v.1) Subtype.val_injective
  have hO : ∏' v : {v // v ∉ s}, f v.1 = Real.exp (∑' v : {v // v ∉ s}, Real.log (f v.1)) :=
    (Real.rexp_tsum_eq_tprod (f := fun v : {v // v ∉ s} => f v.1) (fun v => hpos v.1) hls).symm
  have hT : ∏ p : ↥s, f p.1 = Real.exp (∑ p : ↥s, Real.log (f p.1)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => (Real.exp_log (hpos _)).symm
  have hsplit : ∑ p : ↥s, Real.log (f p.1) + ∑' v : {v // v ∉ s}, Real.log (f v.1) = ∑' v, Real.log (f v) := by
    rw [Finset.sum_coe_sort s (fun x => Real.log (f x))]
    exact hlog.sum_add_tsum_compl (s := s)
  rw [hO, hT, ← Real.exp_add, hsplit, Real.rexp_tsum_eq_tprod hpos hlog]

theorem locOf_al_eq (hEta : EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    (locOf X u u' ψ).al = ∏' q, alpD u u' q := by
  obtain ⟨hpos, hlog⟩ := summable_log_alpD hk u u'
  have he : ∀ v, alX X u u' v = alpD u u' (plEquiv X v) := alX_eq X hEta u u'
  have hxpos : ∀ v, 0 < alX X u u' v := fun v => (he v).symm ▸ hpos _
  have hxlog : Summable fun v => Real.log (alX X u u' v) := by
    have h1 : Summable fun v => Real.log (alpD u u' (plEquiv X v)) := (plEquiv X).summable_iff.2 hlog
    exact h1.congr fun v => by rw [he v]
  have hS := prod_split (alX X u u') (Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hxpos hxlog
  have hR : ∏' v, alX X u u' v = ∏' q, alpD u u' q := by
    rw [tprod_congr he]
    exact (plEquiv X).tprod_eq (alpD u u')
  rw [← hR, ← hS]
  rfl

end Formalism.L2.SG.Pf.AlTie

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem AlTieC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hEta : AlTie.EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq := by
  unfold AlTieC
  exact AlTie.locOf_al_eq X hEta hk u u' ψ

theorem AlTieC_of_loc {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq :=
  AlTieC_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (AlTie.etaTie_of X hL) hk

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem mem_span_aaF {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c)
    {y : (D.s.atP p).Ep}
    (hy : y ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E))) :
    (D.s.atP p).ιE N * y ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D c : FractionalIdeal _ _) : Set D.host.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨x * N, hN x hx, ?_⟩
    rw [map_mul, mul_comm]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul o y _ hy =>
    have e : (D.s.atP p).ιE N * (o • y) = o • ((D.s.atP p).ιE N * y) := by
      show _ * ((o : (D.s.atP p).Ep) * y) = (o : (D.s.atP p).Ep) * (_ * y)
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hy

theorem loc_int {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c) :
    ∃ o ∈ (Z.M p).L.O, (D.s.atP p).ιE N * frFac Z.δ p b = frFac Z.δ p c * o := by
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z
  have hb : frFac Z.δ p b ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E)) := by
    rw [hD p b]
    exact Submodule.subset_span rfl
  have h := mem_span_aaF Z p hN hb
  rw [hD p c, Submodule.mem_span_singleton] at h
  obtain ⟨o, ho⟩ := h
  refine ⟨o, o.2, ?_⟩
  rw [← ho]
  show (o : (D.s.atP p).Ep) * frFac Z.δ p c = frFac Z.δ p c * o
  ring

def locU (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * N.map (D.s.atP p).ιE *
    Matrix.diagonal (frFac Z.δ p)

theorem locU_apply (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (c b : Fin (D.R.rS + 1)) :
    locU Z p N c b = Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c b) * frFac Z.δ p b := by
  simp [locU, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem locU_int (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : ∀ a b, b < a → N a b = 0) (hd : ∀ a, N a a = 1)
    (hN : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c) :
    (∀ a, locU Z p N a a = 1) ∧ (∀ a b, b < a → locU Z p N a b = 0) ∧ ∀ a b, locU Z p N a b ∈ (Z.M p).L.O := by
  have hu : ∀ a, Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 := fun a =>
    Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [locU_apply, hd, map_one, mul_one, hu]
  · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
  · rcases lt_trichotomy a b with h | h | h
    · obtain ⟨o, ho, he⟩ := loc_int Z p (hN a b h)
      rw [locU_apply, mul_assoc, he, ← mul_assoc, hu, one_mul]
      exact ho
    · subst h
      rw [locU_apply, hd, map_one, mul_one, hu]
      exact Subring.one_mem _
    · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
      exact Subring.zero_mem _

end Loc

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Attr

variable {D : D7} {X : HidaSetting D}

abbrev GTu (Y : Full X) (u : D.what₂.Word) : Type :=
  GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)

def jT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ :=
  D.R.rS - Module.finrank D.host.E (Isp (lf D (X.Fu u)).fl (frq X t.rep).fl)

def labT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ → D.host.E :=
  fun l => if l ≤ jT t then Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l else 0

def relSet (Y : Full X) (u : D.what₂.Word) : Set (GTu Y u) := (Y.tO u u).degSet ∩ {t | t.relevant}

def massC (Y : Full X) (u : D.what₂.Word) : ℝ := massRows D (X.Fu u) (Y.what₂ u)

def dpiC (X : HidaSetting D) (u : D.what₂.Word) : ℝ := (Module.finrank ℂ (X.Vpi u) : ℝ)

def H1C (large₂ : SizeData₂ D) (CH : ℝ) : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ))

end Attr

section Steps

def TypeAt {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (CH Cs C Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * ((k2a large₂ CH Cs C j' δ' * k2e large₂ CH Ch Cp j' δ') *
        (k2a large₂ CH Cs C j'' δ'' * k2e large₂ CH Ch Cp j'' δ''))

def IrrVecC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    ∀ t ∈ (Y.tO u u).degSet, ¬ t.relevant → (Y.tO u u).vec t = 0

def JPosC : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ t ∈ relSet Y u, 1 ≤ jT t

def DelC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
        k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2

def CosetsC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Cc : ℝ, 0 ≤ Cc ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
        (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
        ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

def DimFormC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    0 ≤ (Y.tO u u).Gam1 ∧ (Y.tO u u).Gam1 * massC Y u * dpiC X u ≤ Formalism.L2.SG.RowsConc.duC X Y u

def PgLeC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.PgC Y ≤ 2

end Steps

end Formalism.L2.SG.KappaOffDiagonal
end
end
