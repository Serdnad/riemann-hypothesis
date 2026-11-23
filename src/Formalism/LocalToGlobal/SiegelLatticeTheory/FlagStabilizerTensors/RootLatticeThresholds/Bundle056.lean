module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle093
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle099
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinJB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotGeo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlockScaling
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeRelTr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVFix
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle045
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataX

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DvPosC : Prop := ∀ {D : D7} (X : HidaSetting D) (v : NumberField.InfinitePlace X.B.I.F), 0 < X.dv v

theorem recPosC_of_dv {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hDv : DvPosC) (hX : HypX X hb FdN FdN' u u') :
    RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have hTie := hX.1
  have hcol := (inColumnsAt_holds X hb hK FdN FdN' u u' X0 (Formalism.L2.SG.LocVol.locOf X u u' ψ)
    ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < Formalism.L2.SG.RealObj.degX X
    unfold Formalism.L2.SG.RealObj.degX
    exact Finset.prod_pos fun v _ => hDv X v
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u)
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u')
  · exact massH_pos X u
  · exact massH_pos X u'
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d = _ from hcol.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u))
      (div_pos (covolH_pos X hb u hTie) (mul_pos (volH_pos X hb u hTie) (muHpp_pos X hb hK u)))
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d' = _ from hcol.2.2.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u'))
      (div_pos (covolH_pos X hb u' hTie) (mul_pos (volH_pos X hb u' hTie) (muHpp_pos X hb hK u')))

end Formalism.L2.SG.Pf.MassDataX

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SpectralTiesReal
open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensNonnegAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    0 ≤ supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p

theorem massDataPosAll_of (hP : ProdConvAll) (hSW : PI.VolStabS.MassDataS.SWXS) (hDv : Formalism.L2.SG.Pf.MassDataX.DvPosC)
    (hDN : DensNonnegAll) : MassDataPosAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hst hCT hdet hC hTh _
  have hK : T.X.LevelSubgroupNormalized := hCT.1
  have hV : 0 < T.X.volK2 := ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hX : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, hK, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of (hL := Formalism.L2.SG.Pf.MassDataX.locHaarPosC_holds ..)
    (hCv := Formalism.L2.SG.Pf.MassDataX.covolPosC_of (hSW := hSW) (hψ := T.ψ_char) (hC := T.measCompat)
      (hT := T.measTie) (hdet := hdet) ..)
    (hQv := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of T.X T.hb T.Y u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hK hV)
    (hR := Formalism.L2.SG.Pf.MassDataX.recPosC_of_dv T.X T.hb T.Y.hK _ _ u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hDv hX)
    (hP := hP D T u u' hne hst) (hCoo := Formalism.L2.SG.Pf.MassDataPos.cooOf_pos T.X u u')
    (hκ := Formalism.L2.SG.WConst.kapN_pos) (hsd := hDN D T u u' Lsp ϖ) (hC := hC) (hTh := hTh) ..

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

section

noncomputable section

open scoped Classical
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.LoopBPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X}

theorem isFundR_fundOf {u u' : D.what₂.Word} (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') : LoopTerm.IsFundR s (TermOp.FundOf s) := by
  obtain ⟨hm, hex, huniq⟩ := KappaOffDiagonal.fundOf_spec (Closed.FundExistsC_holds D X Y u u') s
  refine ⟨hm, fun r _ => ?_⟩
  obtain ⟨q, hq, hqr⟩ := hex r
  refine ⟨q, ⟨hq, hqr⟩, fun q' hq' => ?_⟩
  have hmem : q' * q⁻¹ ∈ TermOp.ROinf s :=
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).mul_mem hq'.1
      ((TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).inv_mem hq)
  have e : q' * q⁻¹ * (q * r) = q' * r := by group
  have h1 := huniq (q * r) hqr (q' * q⁻¹) hmem (by rw [e]; exact hq'.2)
  exact mul_inv_eq_one.1 h1

theorem pinAll_holds (u u' : D.what₂.Word) : LoopTerm.PinAll (Y := Y) u u' := by
  intro s hrel hG
  have hAt := LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'
  have hRD := Pf.RowForm.RealDecompL.realDecompC_of X Y u u' hAt
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := Pf.RowForm.realDecompC_gamW X Y u u' hRD s hrel hG
  obtain ⟨μw, hH, hmap⟩ := NGPin.pinned_at X u u' (NGPin.pinHaarEx_of_place NGPin.placeHaar_holds) hpt
  obtain ⟨w0, hw0⟩ := hAt s.toTerm hG hrel
  have hw : s.toTerm.atPt (PairVal.ptOf s.toTerm) := PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  refine ⟨⟨PairVal.ptOf s.toTerm, μw.map (fun y => g * y * g⁻¹), TermOp.FundOf s⟩, hw, ?_, isFundR_fundOf s⟩
  exact ⟨RealObj.gamW X u u' (PairVal.ptOf s.toTerm), g, g', μw, NGPin.isPtRep_gamW X u u' hpt, hg, hg', hdec, hH,
    hmap, rfl⟩

section Covol

open Set TermOp TermOp.Vanish

theorem roinf_sub_rset {u u' : D.what₂.Word} (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') {q : X.B.I.Ginf} (hq : q ∈ ROinf s) : q ∈ Rset s := by
  have hs0 : q ∈ ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin := hq
  obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
  have hl : RatLink X (s.pt⁻¹ * z * s.pt) (s.lin⁻¹ * n * s.lin) :=
    ratLink_mul X (ratLink_mul X (ratLink_inv X s.rep.2.1) hz) s.rep.2.1
  have hs2 := Pf.nLamNinf_holds D X u' s.lam' _ _ hl hn'
  rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
  exact ⟨hzs ▸ Pf.nLamNinf_holds D X u s.lam z n hz hn, hs2⟩

theorem stCoord_cont (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) :
    Continuous (RealObj.stCoord X u' w γ) := by
  unfold RealObj.stCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun v => continuous_pi fun p => continuous_const.mul ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp
    ((continuous_const.mul continuous_id).mul continuous_const)))

theorem muStab_compact (w : Point D.host.E (D.R.rS + 1)) {C : Set (InfinitePlace X.B.I.F → RealObj.FreeE w → ℂ)}
    (hC : IsCompact C) : RealObj.muStab X w C < ⊤ := by
  have e : RealObj.muStab X w = Measure.pi fun _ => Measure.pi fun _ =>
      ((D.host.ka / (X.B.g : ℝ) / Real.pi).toNNReal) • (volume : Measure ℂ) := rfl
  rw [e]
  exact hC.measure_lt_top

theorem covolPos_holds (u u' : D.what₂.Word) : LoopTerm.CovolPos (Y := Y) u u' := by
  intro s hrel hG w μR K hw hP hK
  obtain ⟨γw, g, g', μw, hrep, hg, hg', hdec, hH, hmap, rfl⟩ := hP
  obtain ⟨hσ, h0, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  have := TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  have hcc : Continuous fun y : X.B.I.Ginf => g * y * g⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
  have hcm := hcc.measurable
  have hRm : MeasurableSet (Rset s) := (Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : (μw.map fun y => g * y * g⁻¹) (Rset s)ᶜ = 0 := by
    rw [Measure.map_apply hcm hRm.compl]
    apply measure_mono_null _ hconc
    intro y hy hySt
    exact hy (LoopTerm.stInf_conj hg hg' hdec hySt)
  have hinv : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹).map (fun x => q * x) = μw.map fun y => g * y * g⁻¹ := by
    intro q hq
    have hq' := LoopTerm.stInf_conj_inv hg hg' hdec (roinf_sub_rset s hq)
    rw [Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, ∀ B, MeasurableSet B →
      (μw.map fun y => g * y * g⁻¹) ((fun x => q * x) ⁻¹' B) = (μw.map fun y => g * y * g⁻¹) B := by
    intro q hq B hB
    rw [← Measure.map_apply (measurable_const_mul q) hB, hinv q hq]

  have hpos : (μw.map fun y => g * y * g⁻¹) K ≠ 0 := by
    intro hK0
    have hd := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
      (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) Set.univ K MeasurableSet.univ hKm hKu
    have hz : (μw.map fun y => g * y * g⁻¹) Set.univ = 0 := by
      rw [hd]
      have : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
          (μw.map fun y => g * y * g⁻¹) (Set.univ ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K) = 0 := by
        intro q
        rw [Set.univ_inter, hpre q q.2 K hKm, hK0]
      simp only [this, tsum_zero]
    rw [Measure.measure_univ_eq_zero, Measure.map_eq_zero_iff hcm.aemeasurable] at hz
    exact h0 hz

  obtain ⟨K0, hK0c, hK0⟩ := rational_cocompact_holds D X Y u u' s
  have hK0m : MeasurableSet K0 := hK0c.isClosed.measurableSet
  have h1 : (μw.map fun y => g * y * g⁻¹) K ≤ ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
    calc (μw.map fun y => g * y * g⁻¹) K = (μw.map fun y => g * y * g⁻¹) (K ∩ Rset s) :=
          (measure_inter_conull hRc).symm
      _ ≤ (μw.map fun y => g * y * g⁻¹) (⋃ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
            K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hK0 r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
          X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hB : MeasurableSet (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
        X.B.I.Ginf) * x) ⁻¹' K) := hK0m.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hB]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) K0 K hK0m hKm hKu
  have h4 : ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) K0 := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin)).tsum_eq
      (fun q => (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  have hC : IsCompact ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0) := by
    have e : (fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0 = (fun k => g⁻¹ * k * g) '' K0 := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy; exact ⟨g * y * g⁻¹, hy, by group⟩
      · rintro ⟨k, hk, rfl⟩; convert hk using 1; group
    rw [e]
    exact hK0c.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hfin : (μw.map fun y => g * y * g⁻¹) K0 < ⊤ := by
    rw [Measure.map_apply hcm hK0m]
    have hsc := stCoord_cont u' w γw
    have hI : IsCompact (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := hC.image hsc
    calc μw ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)
        ≤ μw (RealObj.stCoord X u' w γw ⁻¹' (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0))) :=
          measure_mono (Set.subset_preimage_image _ _)
      _ = RealObj.muStab X w (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := by
          rw [← hmap, Measure.map_apply hsc.measurable hI.isClosed.measurableSet]
      _ < ⊤ := muStab_compact w hI
  exact ENNReal.toReal_pos hpos (lt_of_le_of_lt (h1.trans_eq h4) hfin).ne

end Covol

end Formalism.L2.SG.Pf.LoopBPin
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

theorem jointTensorAt_of_carrier (I : CarrierIn X u u') (Mo : ModelsFor (_root_.Formalism.L2.SG.Pf.Carrier.sOf I)) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hN : NuQPin X u u' νq) (hG : JointQuot.StVGeo X u u') (hpin : JointPin.PinCov (CarrierOf I Mo))
    (hRT : JointPinJB.RelTr (CarrierOf I Mo) sc i0 i0') (hOV : JointPinJB.OrbVecAt (CarrierOf I Mo) sc i0 i0')
    (hsc : 0 < sc) (hFX : (CarrierOf I Mo).FromX) (hBase : (CarrierOf I Mo).Base i0 i0')
    (hEmb : ∀ j x, (CarrierOf I Mo).S.emb j (X.ιE x) = X.B.I.φ ((CarrierOf I Mo).τ j) x)
    (hBuilt : (CarrierOf I Mo).Built) :
    JointTensorAt X u u' (_root_.Formalism.L2.SG.Pf.Carrier.sOf I) I.T I.fc I.ν' I.m₀ I.τ I.eP I.eQ sc i0 i0' νq :=
  JointPin.jointTensor_of_pin (CarrierOf I Mo) sc i0 i0' νq hN (JointQuot.stRel_holds X u u')
    (JointQuot.locUni_of X u u' hG) (JointQuot.globProd_of X u u' hG) hpin
    (JointPinJB.jointBridge_of_open _ sc i0 i0' hRT hOV) hsc hFX hBase hEmb hBuilt

theorem jointTensorAt_carrierInOf (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (_root_.Formalism.L2.SG.Pf.Carrier.sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hN : NuQPin X u u' νq) (hG : JointQuot.StVGeo X u u')
    (hpin : JointPin.PinCov (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo))
    (hsc : 0 < sc)
    (hFX : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX)
    (hBase : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Base i0 i0')
    (hEmb : ∀ j x, (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.emb j
      (X.ιE x) = X.B.I.φ ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).τ j) x)
    (hBuilt : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Built) :
    JointTensorAt X u u' (_root_.Formalism.L2.SG.Pf.Carrier.sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀))
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).T
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).fc
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).ν'
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).m₀
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).τ
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).eP
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).eQ sc i0 i0' νq := by
  have hMP : MeasPinAt X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0' :=
    Formalism.L2.SG.Pf.Carrier.measPinAt_of X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo
      sc hsc i0 i0' hFX hBase hEmb (fun _ => (hBuilt.2 _).2.2.1)
  refine jointTensorAt_of_carrier _ Mo sc i0 i0' νq hN hG hpin ?_ ?_ hsc hFX hBase hEmb hBuilt
  · intro h1 h2 h3 h4 h5
    exact relTr_carrierOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0' h1 h2 h3 h4 h5
  · intro h1 h2 h3 h4 h5
    exact orbVecAt_carrierOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0'
      (fun v => (h5.2 _).2.2.1) hMP h1 h2 h3 h4


open scoped Matrix in
open Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf in

theorem jointTensorAt_ITcMo (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (Mo : ModelsFor (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (sc : ℝ) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq)
    (hpin : JointPin.PinCov (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo))
    (hsc : 0 < sc) (hBuilt : (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo).Built) :
    JointTensorAt X u u' (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).ν'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).m₀
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ sc i0 i0' νq := by
  have hG : JointQuot.StVGeo X u u' :=
    JointQuot.stVGeo_of_sec X u u' (Formalism.L2.S.L6.UnitaryStandardVectors.stVSec_holds X u u')
  have hFX := BaseOf.fromX X C u u' e he hv CA de de' l grid grid1 fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀ Mo
  have hQ : ∀ v, (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Q v *
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Qi v = 1 :=
    fun v => (isTransp_cs (Formalism.L2.SG.Pf.torTie X) C (X.pl v)).2.1
  have hBase := base_carrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo i0 i0' hQ hi
    (fun j => rfl) (fun j => rfl)
  have hEmb := emb_carrierInOf e he hv C CA de de' l grid grid1 (towersOf X C u u' e) (Tz_towersOf_base_eq_T X C u u' e) fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀
  exact jointTensorAt_carrierInOf X u u' e he hv C CA de de' l grid grid1 (towersOf X C u u' e)
    (Tz_towersOf_base_eq_T X C u u' e) fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀ Mo sc i0 i0' νq hN hG hpin hsc hFX hBase hEmb hBuilt

theorem TT_nonneg (I : CarrierIn X u u') (v : Fin (_root_.Formalism.L2.SG.Pf.Carrier.sOf I).f) : 0 ≤ (Formalism.FourierDecayAlt.D.parOf (_root_.Formalism.L2.SG.Pf.Carrier.sOf I) v).TT := by
  show 0 ≤ (((D.mem u).A.T : ℕ) : ℝ) * (((D.mem u').A.T : ℕ) : ℝ)
  positivity

def modelsOf (I : CarrierIn X u u') : ModelsFor (_root_.Formalism.L2.SG.Pf.Carrier.sOf I) where
  L := fun v => (Formalism.FourierDecayAlt.P.level_exists_alt (Formalism.FourierDecayAlt.D.parOf (_root_.Formalism.L2.SG.Pf.Carrier.sOf I) v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf (_root_.Formalism.L2.SG.Pf.Carrier.sOf I) v)) (Formalism.FourierDecayAlt.P.analytic_laws _ _ (TT_nonneg I v))).choose
  j := fun _ _ => 0
  lam := fun _ _ => 0
  c := Formalism.L2.SG.Pf.CarrierT.cutStd
  Cm := fun _ => 0
  σ := fun _ => 0
  Lw := fun _ _ => 0
  Ll := fun _ _ _ => 0
  Ll' := fun _ _ _ => 0


open scoped Matrix in
open Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf in

theorem jointTensor_compact_test (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (sc : ℝ) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq)
    (hpin : JointPin.PinCov (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      (modelsOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))))
    (hsc : 0 < sc) (hBuilt : (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      (modelsOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))).Built) :
    JointTensorAt X u u' (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).ν'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).m₀
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ sc i0 i0' νq :=
  jointTensorAt_ITcMo X C u u' e he hv CA de de' l grid grid1 fc c i0 i0' hi Θ TP A₀ (modelsOf _) sc νq hN hpin hsc hBuilt

end Formalism.L2.SG.Pf.CarrierXAll
end
end
