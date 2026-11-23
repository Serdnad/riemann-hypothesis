module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKF0IffGapIn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle438
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle200
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle399
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle410
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle274
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle420
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle450
public import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section


theorem _root_.GlobalTheory.T.normalisingConstantsProductHyp_proof : GlobalTheory.TypeAsm.ConstC := by
  first | exact @GlobalTheory.LocalConst.constC | exact GlobalTheory.LocalConst.constC | (intros; apply GlobalTheory.LocalConst.constC <;> assumption)
end

section

namespace GlobalTheory.GapIn

theorem hyp_of_uniqGap : GlobalTheory.GapIn.UniqGap → GlobalTheory.GapIn.Hyp :=
  fun h => ⟨CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap, h, Formalism.L2.SG.OwnFacts.factMultOne.out,
    Formalism.L2.SG.OwnFacts.FD.factDsigHC.out⟩

end GlobalTheory.GapIn
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.FamDlGap

theorem ptDl_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  have hA : GlobalTheory.GapIn.AmpKF0 := GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds
  have hCC : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  obtain ⟨C, hC⟩ := GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1
  refine ⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, hm1, -, -, hrd, -⟩ := hx0 x hx i
  have hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ) := (le_max_left _ _).trans hm1
  have hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := (le_max_right _ _).trans hm1
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hmm⟩
  intro hH0
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0

end GlobalTheory.FamDlGap
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs
open scoped Classical

namespace GlobalTheory.FamGen

open Formalism.MainNotions.S.Lat GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_clsLoc_self {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) {r : ℕ} (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Y0 ∈ clsLoc M Y0 := by
  have hI : IntUni M (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := by
    refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun a b => ?_⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  refine ⟨1, 1, hI, hI, fun a b => ?_, ?_⟩
  · rw [sub_self]; exact Submodule.zero_mem _
  · rw [Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]

theorem exists_famTie : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), (∀ t ∈ TS, t.G ≠ 0) → (∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') → ∀ t₀ ∈ TS, t₀.relevant → ∃ Fm : LocFam (zOf Y) Cl (NuC D), FamTie TS cls (nmlOf Y u u') (ptPN t₀) Fm ∧ (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) ∧ (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t) ∧ (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ c, 0 ≤ Fm.rw c) := by
  intro D X Y u u' Cl TS cls hG hrow t₀ ht₀ hrel
  obtain ⟨w, hw, hat, hfin⟩ := GlobalTheory.T.terms_at_point_of_relevant_term_relevant_finite D X Y u u' t₀ (hG t₀ ht₀) hrel
  have hRL : IsRowLat D (X.Fu u) t₀.toTerm.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  obtain ⟨-, hG0, hcell0⟩ := hat t₀ rfl
  obtain ⟨F00, F'0, F'1, FP, d0, hn, hZ, -, hcell1, hp, hfinP⟩ :=
    GlobalTheory.T.baseData_of_global_term D (zOf Y) u u' (X.Fu u) t₀.toTerm.lam hRL (Quot.out t₀.toTerm.cls).1
      (Quot.out t₀.toTerm.cls).2 hG0 w hcell0
  have hreps := fun p => GlobalTheory.LocOver.orbit_reps_over ((zOf Y).M p) ((zOf Y).agree p).1 (locH (zOf Y) p) D.R.rS (FP p)
  let R : ∀ p : PlF D, LocNG.Reps (FP p) := fun p => (hreps p).2.1.some
  let LT : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ∀ p : PlF D, Formalism.MainNotions.S.Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS :=
    fun s p => locU (zOf Y) p s.lam (lf D (X.Fu u)) (Quot.out s.cls).1 (Tu D u) (Tu D u')
  let rho : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ∀ p : PlF D, LocNG.Datum (FP p) :=
    fun s p => if h : ∃ d ∈ (R p).RD, Over (FP p) d (LT s p) then h.choose else d0 p

  have hover : ∀ t : TauC Y u u', ptPN t = ptPN t₀ → ∀ p, ∃ d, Over (FP p) d (LT t.toTerm p) := by
    intro t ht p
    obtain ⟨-, hGt, hct⟩ := hat t ht
    exact GlobalTheory.T.globalTerm_lies_over_localDatum_after_isometry D (zOf Y) u u' (X.Fu u) t.toTerm.lam ((Y.rowsOK u).1 t.lam t.mem) (Quot.out t.toTerm.cls).1
      (Quot.out t.toTerm.cls).2 hGt w F00 F'0 hct hZ p (FP p) (hp p).1
  have hrho : ∀ t : TauC Y u u', ptPN t = ptPN t₀ → ∀ p, rho t.toTerm p ∈ (R p).RD ∧ Over (FP p) (rho t.toTerm p) (LT t.toTerm p) := by
    intro t ht p
    obtain ⟨d, hd⟩ := hover t ht p
    obtain ⟨y, hy, hyd⟩ := (R p).hRD.2.1 d (Set.mem_univ _)
    have hex : ∃ d ∈ (R p).RD, Over (FP p) d (LT t.toTerm p) := ⟨y, hy, (hreps p).2.2 d y _ ((hreps p).1.symm hyd) hd⟩
    have e : rho t.toTerm p = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec

  let γ := ptPN t₀
  let Pf : Finset (PlF D) := hfinP.toFinset
  let Om : Finset {p // p ∈ Pf} := Pf.attach.filter (fun p => ¬ (FP p.1).PrimeTo)
  let Ds : ∀ p : PlF D, Finset (LocNG.Datum (FP p)) := fun p => hfin.toFinset.image (fun s => rho s p)
  have hmemDs : ∀ t : TauC Y u u', ptPN t = γ → ∀ p, rho t.toTerm p ∈ Ds p := fun t ht p =>
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨t, ht, rfl⟩)
  let dat : Cl → NuC D → Option (∀ p : {p // p ∈ Pf}, {d // d ∈ Ds p.1}) := fun c ν =>
    if h : ∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν then
      some (fun p => ⟨rho h.choose.toTerm p.1, hmemDs _ h.choose_spec.2.2.1 p.1⟩) else none
  let rw : Cl → ℝ := fun c => if h : ∃ t ∈ TS, cls t = c then (Formalism.L2.SG.TermOp.wt h.choose) ^ 2 else 0
  let ngenL : PlF D → ℝ := fun p => (ngenLoc (R p) (d0 p) (clsLoc ((zOf Y).M p)
    ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1)))).toReal
  let Fm0 : LocFam (zOf Y) Cl (NuC D) := ⟨Pf, Om, FP, R, d0, Ds, ngenL, 0, rw, dat⟩
  let Fm : LocFam (zOf Y) Cl (NuC D) := { Fm0 with V0 := if h : ∃ v, OrbitFamilyIdentityAt Fm0 v then h.choose else 0 }
  have hDs : ∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD := by
    intro p _ d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨t, ht, rfl⟩ := hfin.mem_toFinset.1 hs
    exact (hrho t ht p).1
  have hnotP : ∀ p, p ∉ Pf → (FP p).PrimeTo ∧ LocNG.IsTermOver (FP p) (d0 p) ⟨lattice₂ D (zOf Y).M p t₀.toTerm.lam,
      scaled (zOf Y) p (frame F00), scaled (zOf Y) p (frame F'0), ((Tu D u : ℕ) : (D.s.atP p).Fp),
      ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩ := by
    intro p hp'
    by_contra hc
    exact hp' (hfinP.mem_toFinset.2 hc)
  refine ⟨Fm, ⟨w, F00, F'0, F'1, hw, hDs, rfl, hn, hZ, fun p => (hp p).1, ?_, fun p hp' => (hnotP p hp').1, ?_,
    ⟨t₀, ht₀, rfl, fun p _ => (hp p).2.2.1⟩, fun p _ => ⟨_, (hp p).2.2.1⟩,
    ⟨t₀.toTerm.lam, hRL.1.1.toIsLattice, fun p hp' => (hnotP p hp').2⟩, ?_, hcell1, fun p _ => ⟨rfl, d0 p, _, (hp p).2.2.1, ?_⟩⟩,
    fun p _ => (hp p).2.1, fun p _ => ⟨d0 p, _, (hp p).2.2.1⟩, hDs, fun c => ?_⟩
  · intro p
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_attach _ _))
  · intro p hp' t _ ht
    obtain ⟨-, hGt, hct⟩ := hat t ht
    obtain ⟨d, g, hg, d', hdd', hto⟩ := GlobalTheory.T.globalTerm_lies_over_localDatum_after_isometry D (zOf Y) u u' (X.Fu u) t.toTerm.lam ((Y.rowsOK u).1 t.lam t.mem)
      (Quot.out t.toTerm.cls).1 (Quot.out t.toTerm.cls).2 hGt w F00 F'0 hct hZ p (FP p) (hp p).1
    have hpr := (hnotP p hp').1
    have hrel' : LocNG.Datum.Rel (d0 p) d' :=
      GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo ((zOf Y).M p) ((zOf Y).agree p).1 (locH (zOf Y) p) D.R.rS D.R.k (FP p) (rank_Vp p) (hp p).2.1 hpr
        (d0 p) d' _ _ (hp p).2.2.1 hto
    exact ⟨g, hg, d', hrel', hto⟩
  · intro c ν
    by_cases h : ∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν
    · have e : Fm.dat c ν = some (fun p => ⟨rho h.choose.toTerm p.1, hmemDs _ h.choose_spec.2.2.1 p.1⟩) := dif_pos h
      rw [e]
      obtain ⟨hc1, hc2, hc3, hc4⟩ := h.choose_spec
      refine ⟨h, fun t ht hct hpt hnt => ⟨fun p _ => ?_, ?_⟩⟩
      · have hsame := GlobalTheory.T.terms_same_row_same_weight_same_localData D X Y u u' h.choose t (hG _ hc1) (hrow _ hc1 t ht (hc2.trans hct.symm))
        obtain ⟨g, hg, d', hdd', hto⟩ := hsame.2 (hc4.trans hnt.symm) p (FP p) (hp p).2.1 _ (hrho _ hc3 p).2
        exact ⟨g, hg, d', hdd', hto⟩
      · have hc : ∃ t ∈ TS, cls t = c := ⟨t, ht, hct⟩
        have e2 : Fm.rw c = (Formalism.L2.SG.TermOp.wt hc.choose) ^ 2 := dif_pos hc
        rw [e2]
        obtain ⟨hh1, hh2⟩ := hc.choose_spec
        rw [(GlobalTheory.T.terms_same_row_same_weight_same_localData D X Y u u' hc.choose t (hG _ hh1) (hrow _ hh1 t ht (hh2.trans hct.symm))).1]
    · have e : Fm.dat c ν = none := dif_neg h
      rw [e]
      exact h
  · show (locH (zOf Y) p).Zhat (locU (zOf Y) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f
      (locU (zOf Y) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f' ∈ _
    have hm := mem_clsLoc_self ((zOf Y).M p) ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1))
    convert hm using 3
    all_goals first | rfl | exact (hp p).2.2.2
  · show 0 ≤ (if h : ∃ t ∈ TS, cls t = c then (Formalism.L2.SG.TermOp.wt h.choose) ^ 2 else 0)
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

end GlobalTheory.FamGen
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.product_l2_positive : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → 0 < (X.muN u (Y.FN u)).toReal → 0 < (X.muH u Set.univ).toReal → (∀ τ, 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) ∧ (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
  first | exact @GlobalTheory.ProductL2.l2prod | exact GlobalTheory.ProductL2.l2prod | (intros; apply GlobalTheory.ProductL2.l2prod <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg.CritVand

theorem thrE_add_one_lt (R : Formalism.BasicNotions.Ranks) (h : 1801 ≤ R.r) :
    Formalism.MainNotions.GapDS.thrE (epsSH R) + 1 < 16 * (R.r : ℝ) ^ 19 := by
  have hd : ((2 * R.rS + R.k + 1 : ℕ) : ℝ) = R.r := by exact_mod_cast dimS_eq R
  have hx : (1801 : ℝ) ≤ R.r := by exact_mod_cast h
  have h1 := Formalism.MainNotions.GapDS.thrE_le (epsSH R) (by rw [hd]; linarith)
  rw [hd] at h1
  have h3 : (1 : ℝ) ≤ (R.r : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have h16 : (R.r : ℝ) ^ 3 ≤ (R.r : ℝ) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

theorem vv_eq_vand_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl →
    Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  refine ⟨29, fun D large₂ C' Cl Cg cb Cu cT CT hC' hCl hT hH _ τ => ?_⟩
  have hG := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hgap := Formalism.L2.SG.Pf.WuBL.gapAtLeast_of D.R (D.hc τ) (hG.2 τ)
  have hds := GlobalTheory.T.formalDegree_eq_harishChandra_of_gap D hT τ _ (Formalism.L2.Col.lamSH_isHCParam (D.hc τ)) hgap (thrE_add_one_lt D.R hG.1)
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hds, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq D.R]
  exact div_mul_cancel₀ _ hSF.ne'

end GlobalTheory.Core.Deg.CritVand
end
