module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle039
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ClauseAOfIdentityFlag
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle008
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdScal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle007
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdNP

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Frame

variable (p : PlF D) {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')

theorem locF'_eq (b : Fin (D.R.rS + 1)) : locF' Zd p G b = sF' Zd p b • baseChange₂ D p (frame G b) := rfl

theorem bcP_frameG (b : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame G b) = (((isUnit_sF' Zd p b).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • locF' Zd p G b := by
  rw [locF'_eq, smul_smul, (isUnit_sF' Zd p b).val_inv_mul, one_smul]

theorem frame_csG (i : Fin D.R.rS) : frame G i.castSucc = G.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_lastG : frame G (Fin.last D.R.rS) = G.fl.z := by
  simp [frame, FlagG.fvec]

theorem sF'_last : sF' Zd p (Fin.last D.R.rS) = 1 := by
  unfold sF'
  rw [frFac_last' Zd p, mul_one]
  unfold TermLoc.sgnP'
  split
  · exact sgnP_last p
  · simp

theorem locF'_last : locF' Zd p G (Fin.last D.R.rS) = baseChange₂ D p G.fl.z := by
  rw [locF'_eq, sF'_last, one_smul, frame_lastG]

theorem bcP_X' {x : (VS D).V} (hx : x ∈ Xsp G) : baseChange₂ D p x ∈ (locH Zd p).X (locF' Zd p G) := by
  change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_csG, bcP_frameG Zd p G]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChangeAt_perp' {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p G)) := by
  show ∀ w ∈ (locH Zd p).X (locF' Zd p G), (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [locF'_eq, frame_csG, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end Frame

theorem coef_intG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame G a ∈ Λ) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame G a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) *
      ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) • locF' Zd p G a := by

    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, bcP_frameG Zd p G, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (locF' Zd p G)) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) •
        locF' Zd p G a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (isUnit_sF' Zd p (Fin.last D.R.rS)) (sF'_last Zd p)
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_yG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (hSD : BwdNA.SD (VS D) Λ)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (hzX : G.fl.z ∉ Xsp G) :
    ∃ y ∈ Λ, y ∈ orth (VS D) (Xsp G) ∧ (VS D).hT y G.fl.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f G.fl.z)⁻¹ • f
  have hρz : ρ G.fl.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp G, ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp G).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame G i.castSucc) = 0 := fun i => by
    rw [frame_csG]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame G (Fin.last D.R.rS)) = 1 := by
    rw [frame_lastG, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame G))
  have hint : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by

      rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_intG Zd G hprim c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ hΛ hSD U v hint
  have hw : ∀ a, (VS D).hT w (frame G a) = ρ (frame G a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame G a) w, ← h0, ← BwdNA.hsw (VS D) (frame G a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (G.fl.e i), ← frame_csG, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · rw [← frame_lastG, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI
end
end

section

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem absV_prod {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v) : absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact absV_one v
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, absV_mul, ih]

theorem absV_alp_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (h1 : absV v (dV v) = 1)
    (r : ℕ) (i : Fin (r + 1)) : absV v (alp v r i) = 1 := by
  rw [absV_alp, h1, Real.one_rpow]

section Vols

variable {X} {ψ}

theorem zz_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : ZZX X u u' ψ v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH1, -, hO1⟩ := hN v hv (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  have := hH1
  have hsetZ : ZZOrd (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
        {c | sc (E := X.B.I.E) v (alp v D.R.rS p.1 * alp v D.R.rS p.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  unfold ZZX volS
  rw [if_neg hv, hsetZ, SdW.boxScaleL_holds v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) hfin
    (sdE (E := X.B.I.E) ψ v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => alp v D.R.rS p.1 * alp v D.R.rS p.2)
    (fun p => mul_ne_zero (alp_ne_zero v D.R.rS p.1) (alp_ne_zero v D.R.rS p.2)), hO1, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [absV_mul, absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem uo_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) :
    (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS) (UO (E := X.B.I.E) v D.R.rS)).toReal = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH2, -, hO2⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have hsetU : UO (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun q : UIdx D.R.rS =>
        {c | sc (E := X.B.I.E) v ((alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  rw [hsetU, SdW.boxScaleL_holds v (UIdx D.R.rS) hfin (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS))
    (fun q : UIdx D.R.rS => (alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2)
    (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v D.R.rS q.1.1)) (alp_ne_zero v D.R.rS q.1.2)), hO2, h1,
    one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_mul, absV_inv v (alp_ne_zero v D.R.rS q.1.1), absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem unramified_factor_eq_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : localVolumeUnit X ψ v = 1 := by
  obtain ⟨hH2, hS2, -⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have := hS2
  unfold localVolumeUnit volU
  rw [if_neg hv, localVolumeOrdinary, Measure.prod_prod, ENNReal.toReal_mul, uo_one hN hv h1, one_mul]

theorem pp_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) (l : Fin (D.R.rS + 1)) :
    PPX X u u' ψ l v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_pow, absV_alp_one v h1]
  norm_num

theorem jac_one {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : jacX X v = 1 := by
  unfold jacX jacS
  refine Finset.prod_eq_one fun l _ => ?_
  rw [if_neg hv, mul_one, absV_prod]
  rw [Finset.prod_eq_one fun i _ => by rw [absV_pow, absV_alp_one v h1, one_pow]]
  norm_num

end Vols

theorem VolOneAEC_holds (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : VolOneAEC X u u' ψ := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hT : Set.Finite {v : PlX X | TypAt X v} := (typSet X.B.I.F (D.host.g 0) (D.host.g 1)).finite_toSet
  have hI := differentIdeal_ne_zero' X.B.I.F
  have hD := Ideal.hasFiniteMulSupport hI
  refine (hT.union hD).subset fun v hv => ?_
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Function.mem_mulSupport, not_or, not_not] at hnot
  obtain ⟨htyp, hmax⟩ := hnot
  have h1 : absV v (dV v) = 1 := by rw [absV_dV, hmax, map_one, Nat.cast_one, inv_one]
  exact hv ⟨unramified_factor_eq_one hN htyp h1, zz_one u u' hN htyp h1, fun l => pp_one u u' hN htyp h1 l, jac_one htyp h1⟩

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1c

variable {D : D7} {X : HidaSetting D}

theorem isIdentity_of_equal_flags (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a)
    (hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus)
    (hrel : Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl) : t.isId := by
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'
  have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hfix : FixedHyp D t.lam (lf D (X.Fu u)) := hrow.2.1
  have hPD : TermDef.PD D t.lam (lf D (X.Fu u)) u (frq X t.rep) := t.rep.2.2.2.2
  have hlift : IsLift t.lam (frq X t.rep) := hPD.1
  have hadm : IsAdmissible t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) := hPD.2.1
  have hconv : IsFixedConv t.lam (gS D) (frq X t.rep) := hPD.2.2.1
  obtain ⟨c, hcc, he, hz⟩ := id_scal D.host.F D.host.E (hS D) D.R.rS _ (lf D (X.Fu u)).fl (frq X t.rep).fl hT0
    (tie_trace D.sp.cm) hXa hXp hrel
  have hX : (frq X t.rep).fl.X = (lf D (X.Fu u)).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa]; exact hXa _
  obtain ⟨o, ho, N, hN, hoN⟩ := id_unit D.host.E (hS D) D.R.rS _ t.lam (lf D (X.Fu u)) (frq X t.rep) c (p_starConj D)
    hlift.1 hfix.2.2.2.2 hcc hz hX
  have hcong : ∀ i : Fin 2, ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      o - 1 ∈ P.asIdeal := by
    intro i P hP
    refine id_cong D.host.E (hS D) D.R.rS (Tu D u) t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) o hfix.2.1
      hfix.2.2.1.1 hadm (by rw [ho]; exact hz) P ?_ ?_
    · unfold _root_.Formalism.MainNotions.S.Lat.gS
      rw [Nat.cast_mul]
      fin_cases i
      · exact P.asIdeal.mul_mem_right _ hP
      · exact P.asIdeal.mul_mem_left _ hP
    · refine id_coprime_notMem P.asIdeal P.isPrime.ne_top _ _ ?_ hP
      refine (Nat.coprime_primes (D.host.g_prime i) (D.mem u).A.T_prime).2 ?_
      fin_cases i
      · exact (hTg u).1.symm
      · exact (hTg u).2.symm
  obtain ⟨P1, hP1⟩ := id_over D.host.E _ (D.host.g_prime 0)
  obtain ⟨P2, hP2⟩ := id_over D.host.E _ (D.host.g_prime 1)
  have ho1 : o = 1 := id_root (𝓞 D.host.E) o N _ _ P1.asIdeal P2.asIdeal hN hoN (D.host.g_prime 0) (D.host.g_prime 1)
    D.host.g_ne P1.isPrime.ne_top P2.isPrime.ne_top hP1 hP2 (hcong 0 P1 hP1) (hcong 1 P2 hP2)
  have hc1 : c = 1 := by rw [← ho, ho1]; rfl
  subst hc1
  simp only [one_smul] at he hz
  obtain ⟨n, hn, hne⟩ := id_lift D _ t.lam (lf D (X.Fu u)) (frq X t.rep) hfix hlift hconv he hz
  have hzo : (lf D (X.Fu u)).fl.z ∈ orth (hS D) (Xsp (lf D (X.Fu u))) := by
    rw [p_mem_orth]
    exact tie_X_le_ker _ _ (lf D (X.Fu u)).fl.z_orth
  have h3' := hn.2.2 _ hzo
  have hzz : n (lf D (X.Fu u)).fl.z - (frq X t.rep).fl.z =
      (n (lf D (X.Fu u)).fl.z - (lf D (X.Fu u)).fl.z) - ((frq X t.rep).fl.z - (lf D (X.Fu u)).fl.z) := by abel
  refine ⟨frq X t.rep, TermDef.rep_mk (⟨frq X t.rep, hPD⟩ : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u)),
    n, hn, hne, ?_⟩
  rw [hzz]
  exact Submodule.sub_mem _ h3' hz

theorem one_le_index_of_relevant (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) : 1 ≤ jT t := by
  obtain ⟨hr, hG, hid⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  rw [index_eq_normalForm t hN]
  by_contra hj0
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨k1, -, k3⟩ := Formalism.HermitianLatticeCounting.Final.S6.nFJZero _ _ _ _ _ _ c hN.1
  have hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a := fun a => by
    exact (nf_Xa (frq X t.rep).fl (nf_T_ne D u) a).symm.trans
      ((k1 a).trans (nf_Xa (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u) a))
  have k3' : (frq X t.rep).fl.z - c • (lf D (X.Fu u)).fl.z ∈ (lf D (X.Fu u)).fl.X := by
    rw [← normal_form_z_eq (frq X t.rep).fl (nf_T_ne D u),
      ← normal_form_z_eq (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u),
      ← nf_X (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)]
    exact k3
  have hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus :=
    nf_Xplus_eq _ _ (by rw [nf_X_eq, nf_X_eq]; exact hXa _) c hN.1.1 k3'
  exact hid (isIdentity_of_equal_flags hTg Y t hXa hXp (relRepC D X Y u u t hr hG).1)

end ZsC1c

theorem JPosC_holds : JPosC := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hK _ t ht
  refine one_le_index_of_relevant (fun w => ?_) Y t ht

  have hc : Nat.Coprime (D.mem w).A.T (D.host.g 0 * D.host.g 1) := (hK.2.2.2.2.2.2.1 w).2
  have key : ∀ i : Fin 2, D.host.g i ∣ D.host.g 0 * D.host.g 1 → (D.mem w).A.T ≠ D.host.g i := by
    intro i hd h
    rw [h] at hc
    have h1 : Nat.Coprime (D.host.g i) (D.host.g i) := Nat.Coprime.coprime_dvd_right hd hc
    exact (D.host.g_prime i).one_lt.ne' (by simpa [Nat.coprime_self] using h1)
  exact ⟨key 0 (dvd_mul_right _ _), key 1 (dvd_mul_left _ _)⟩

end Formalism.L2.SG.KappaOffDiagonal
end
end

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LocU

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locU_mul (A B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A * locU Z p B = locU Z p (A * B) := by
  ext i j

  simp only [Matrix.mul_apply, locU_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc _ = Ring.inverse (frFac Z.δ p i) * (D.s.atP p).ιE (A i k) *
        (frFac Z.δ p k * Ring.inverse (frFac Z.δ p k)) * (D.s.atP p).ιE (B k j) * frFac Z.δ p j := by ring
    _ = _ := by rw [frFac_mul_inv, mul_one]; ring

theorem locU_sub_one (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A - 1 = locU Z p (A - 1) := by
  ext i j
  simp only [Matrix.sub_apply, locU_apply, map_sub, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [map_one, mul_sub, sub_mul, mul_one, frFac_inv_mul]
  · simp only [map_zero, sub_zero]

end LocU

end Formalism.L2.SG.Pf.FibQ
end
end
