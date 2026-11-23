module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle359
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle343
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle360
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarVolPf
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbability
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem GlobalTheory.RowsOrb.exists_row_of_unimod : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) → ∃ Λ ∈ Y.what₂ u, ∃ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ = L := by
  intro D large₂ X Y u hStd L hL hU hprim
  obtain ⟨hlat, hun⟩ := GlobalTheory.RowsOrb.Glue.glue_isLattice_unimodular D large₂ X hStd L hL hU
  have hgen := GlobalTheory.RowsOrb.ExGenus.mem_genus_of_isUnimodular D large₂ hStd X u _ hlat hun
  obtain ⟨hx, hx0, hlm, hsub⟩ := GlobalTheory.RowsOrb.parts_of_lat D X u L
  have hzL : GlobalTheory.RowsOrb.zb X u ∈ L := by
    have h1 := (hprim 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rwa [one_smul] at h1
  have hzΛ : X.zu u ∈ latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact ⟨GlobalTheory.RowsOrb.zb X u, hzL, rfl⟩
  have hfix0 := (X.Fu_fixed u).2.2.2.1
  have hlf : (lf D (X.Fu u)) = (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) := by
    show (⟨X.Fu u, (X.Fu u).z⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS _) = _
    rw [X.flagZVector u]
  have hfix : FixedHyp D (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
    refine ⟨hlat, hun, ⟨?_, rfl⟩, ?_, ?_⟩
    · show (X.Fu u).z ∈ _
      rw [X.flagZVector u]; exact hzΛ
    · intro P
      rw [hx]
      rw [← hx0, hlf]
      exact hfix0 P
    · intro c hc
      have hc' : ((c • GlobalTheory.RowsOrb.zb X u : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
        rw [Submodule.coe_smul, GlobalTheory.RowsOrb.zb_coe, ← X.flagZVector u]; exact hc
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((hprim c).1 (hsub _ hc'))
      exact ⟨o, ho⟩
  have hrow : IsRowLat D (X.Fu u) (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := ⟨hgen, hfix, hx⟩
  obtain ⟨Λ', ⟨hΛ', γ, hγ, hmap⟩, -⟩ := (Y.rowsOK u).2 _ hrow
  obtain ⟨g, hg⟩ := GlobalTheory.RowsOrb.exists_gz_lmap D X u γ hγ
  exact ⟨Λ', hΛ', g, by rw [hg, hmap, hlm]⟩
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction : VolumeStep → AbsoluteVolume := by
  first | exact @GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | exact GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitary_adelic_quotient_volume_pos_lt_top : VolumeStep → ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ p q : ℕ, HasSig I p q → 2 ≤ p → 0 < I.muA μf fund ∧ I.muA μf fund < ⊤ := by
  first | exact @GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top | exact GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top | (intros; apply GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open Filter Topology
open scoped TensorProduct

namespace GlobalTheory.ThetaVacuumAE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finset_of_mem_nhds {F : Type} [Field F] [NumberField F] {N : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)} (hN : N ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ α ∈ intAf F, (∀ v ∈ S, evalV F v α = 0) → α ∈ N := by
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have h := hc.tendsto (fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) hN
  have h' := mem_map.1 h
  rw [nhds_pi, mem_pi'] at h'
  obtain ⟨I, t, ht, hI⟩ := h'
  refine ⟨I, fun α hα h0 => ?_⟩
  have hm : (fun w => (⟨evalV F w α, hα w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) ∈
      Set.pi (I : Set (HeightOneSpectrum (𝓞 F))) t := by
    intro w hw
    have := mem_of_mem_nhds (ht w)
    convert this using 2
    exact h0 w hw
  exact hI hm

theorem fg_int {E : Type} [Field E] [NumberField E] {M : Submodule (𝓞 E) E} (h : M.FG) : (M.restrictScalars ℤ).FG :=
  Submodule.FG.restrictScalars h

theorem exists_fg_coord {D : D7} (V : HSp D) :
    ∃ M : Submodule ℤ D.host.E, M.FG ∧ ∀ x ∈ L0c D V, ∀ i, x i ∈ M ∧ star (x i) ∈ M := by
  let P : Submodule (𝓞 D.host.E) D.host.E := ⨆ i, V.L0.map ((V.frame.coord i).restrictScalars (𝓞 D.host.E))
  have hP : P.FG := Submodule.fg_iSup _ fun i => V.standardTuple_isLattice.fg.map _
  have hx : ∀ x ∈ L0c D V, ∀ i, x i ∈ P := fun x hx i =>
    Submodule.mem_iSup_of_mem i ⟨_, hx, by simp [Finsupp.single_apply]⟩
  let c : D.host.E →ₗ[ℤ] D.host.E := (starRingEnd D.host.E).toAddMonoidHom.toIntLinearMap
  refine ⟨P.restrictScalars ℤ ⊔ (P.restrictScalars ℤ).map c, (fg_int hP).sup ((fg_int hP).map c), fun x h i =>
    ⟨Submodule.mem_sup_left (hx x h i), Submodule.mem_sup_right ⟨x i, hx x h i, rfl⟩⟩⟩

theorem continuous_tmul (D : D7) (e : D.host.E) :
    Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => (pairA D.host.F 0 α ⊗ₜ[D.host.F] e : AE D) := by
  have hp : Continuous fun β : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 β := continuous_const.prodMk continuous_id
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h := hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D)))
  refine h.congr fun α => ?_
  simp only [Pi.smul_apply', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.ThetaVacuumAE

end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

theorem _root_.GlobalTheory.T.rationalBesselFrame_realPlace_linearIndependent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F), LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  first | exact @GlobalTheory.RationalFrame.frame_linearIndependent | exact GlobalTheory.RationalFrame.frame_linearIndependent | (intros; apply GlobalTheory.RationalFrame.frame_linearIndependent <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)) := by
  first | exact @GlobalTheory.OrbitRel.relEqv | exact GlobalTheory.OrbitRel.relEqv | (intros; apply GlobalTheory.OrbitRel.relEqv <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_flag_scaled_frame_eq_baseChange_flag : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (j : ℕ), Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa j : Set (VS D).V)) = (A p).Fj j := by
  first | exact @GlobalTheory.FlagBaseChange.span_bcP_Xa_eq_Fj | exact GlobalTheory.FlagBaseChange.span_bcP_Xa_eq_Fj | (intros; apply GlobalTheory.FlagBaseChange.span_bcP_Xa_eq_Fj <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthogonal_decomposition_local_nondegenerate : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 := by
  first | exact @GlobalTheory.decomp_orth_complement | exact GlobalTheory.decomp_orth_complement | (intros; apply GlobalTheory.decomp_orth_complement <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.scaled_local_dual_coeff_eq_global_coeff : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (a : Fin D.R.rS) (x : (VS D).V), x ∈ G.fl.X → frFac Z.δ p a.castSucc * (locH Z p).h (baseChange₂ D p x) ((A p).es a) = (D.s.atP p).ιE (G.fl.coefX x a) := by
  first | exact @GlobalTheory.RowLatXS.scaled_local_coef_eq | exact GlobalTheory.RowLatXS.scaled_local_coef_eq | (intros; apply GlobalTheory.RowLatXS.scaled_local_coef_eq <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fractional_ideal_eq_of_local_spans_eq : ∀ (D : D7) (Z : LocDat D) (I J : Submodule (𝓞 D.host.E) D.host.E), I.FG → J.FG → (∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (I : Set D.host.E)) = Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (J : Set D.host.E))) → I = J := by
  first | exact @GlobalTheory.Sloc.fg_eq_of_completions | exact GlobalTheory.Sloc.fg_eq_of_completions | (intros; apply GlobalTheory.Sloc.fg_eq_of_completions <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem covol_formalDegree_eq : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D →
    Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ :=
  fun _D X h hVol hcd hT => Formalism.L2.SG.Pf.DstarVolPf.dstarVol_holds X h hVol hcd hT

end GlobalTheory
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability : ∀ (j : ℕ) (μ : Measure (PI.MtM j)), PI.IsHaarOnM (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ → μ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ (ENNReal.ofReal (volUn j)⁻¹) := by
  first | exact @GlobalTheory.UnitaryVolume.hasDens_unitary | exact GlobalTheory.UnitaryVolume.hasDens_unitary | (intros; apply GlobalTheory.UnitaryVolume.hasDens_unitary <;> assumption)
end
