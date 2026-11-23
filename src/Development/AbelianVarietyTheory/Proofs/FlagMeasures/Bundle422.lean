module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle396
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselDoubleCosetMeasureBigCellEq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle417
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle304
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle338
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle257
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRep
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle418
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle419
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowDoubleCosetInnerDataOneRationalClass
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.GenCoord

theorem generic_iff_locU {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D)
    (t₀ : TauC Y u u') : t₀.generic ↔
      ∀ p, ¬ LocNG.BBne (H := locH Z p) (locU Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')) := by
  have hrows := Y.rowsOK u
  have hBF := Formalism.L2.SG.Pf.big_block_function_holds D u u'
  have hT := Formalism.L2.SG.Pf.bbTie_holds D Z
  have hMI : ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
      (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Formalism.L2.SG.Saturated.MplusIndep Λ (lf D F0) (gS D) F' :=
    fun F0 Λ F' => Formalism.L2.SG.Pf.m_plus_independent _ _ _ _
  have hg := genIffLocBB_of Z hT u u' hBF hMI (X.Fu u) (Y.what₂ u) hrows t₀.toTerm
  show t₀.toTerm.generic ↔ _
  rw [hg]
  refine forall_congr' fun p => not_congr ?_
  have hL := hrows.1 t₀.lam t₀.mem
  refine ((termBBne_iff_loc Z hT hrows hBF (hMI (X.Fu u)) t₀.toTerm p).symm.trans ?_).trans
    (GlobalTheory.T.signedLocalTerm_defect_iff_unsignedLocalTerm Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))
  refine Iff.trans ?_ (hT u u' (X.Fu u) t₀.lam t₀.frame hL t₀.rep.2.2.2.2 (hMI _ _ _) p)
  constructor
  · rintro ⟨F', ⟨h, hm⟩, P, hP, hbb⟩
    refine ⟨P, hP, ?_⟩
    have e := Formalism.L2.SG.TermDef.const_of_mk
      (fun y : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u') =>
        Formalism.L2.SG.Saturated.BBneP t₀.lam (gS D) (lf D (X.Fu u)) y.1 P)
      (fun a b hab => propext (hBF (X.Fu u) t₀.lam hL P a b hab)) hm
    exact e ▸ hbb
  · intro h
    exact ⟨t₀.frame, ⟨t₀.rep.2.2.2.2, rfl⟩, h⟩

theorem generic_iff_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (t₀.generic ↔ G.Gen (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hρ : ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hMv.1
  rw [generic_iff_locU X Y u u' (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) t₀]
  refine forall_congr' fun p => ?_
  obtain ⟨g, hgExt, hgU, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hρ
  have hGv : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := fun h => hG ((GlobalTheory.T.gramInvariant_isometry_unitriangular_moves F00 F'0 _ _ ρ U U' hMv).symm.trans h)
  have hRL : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  obtain ⟨hIT, hTri'⟩ := GlobalTheory.LocOver.locU_isTerm D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hRL
    t₀.frame t₀.rep.2.2.2.2 hGv p
  have hOK : (Y.M p).OK := (Y.agree p).1
  have htIT := GlobalTheory.T.localTerm_move_unitary_isTerm (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g hgU _ hIT
  obtain ⟨hTA, hTB⟩ := GlobalTheory.T.localFrames_movedTerm_unitriangular_change (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 _ _ ρ U U' g _ hMv hgExt hTri'
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (hAt p).1
  rw [← hA1] at hTA
  rw [← hA2] at hTB
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS (FP p)
    (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')))
    htIT hA3.symm hA4.symm hTA hTB
  have hW := ((GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
    (c.c p)).1 d _ hd)
  have hlat := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).2.2.2.2.1 ρ hρ p g t₀.lam hgExt
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
  have hlat' : (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) = (c.c p).lat
      (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))).abelian₂ := hlat
  have hdat := GlobalTheory.HL.DatumOf.datOf_term (G.S p) hW.1
  show _ ↔ (G.S p).BBzero ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam))
  rw [hlat', ← hdat, ← GlobalTheory.T.localTermDefect_ne_iff_move_linearEquiv (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g, hW.2.2]
  exact not_not

end GlobalTheory.HL.GenCoord
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.haar_lie_nilpotent_coordinates : ∀ (k r : ℕ), IsHaarOn (Nset k r) (haarLie (Nset k r) 1) ∧ Set.InjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} ∧ Set.SurjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} Set.univ ∧ (haarLie (Nset k r) 1).map (nCoords k r) = (2 : ℝ≥0∞) ^ (r * (r - 1) + r * (k + 1)) • volume := by
  first | exact @GlobalTheory.SnMass.NEntry.haarLie_entries | exact GlobalTheory.SnMass.NEntry.haarLie_entries | (intros; apply GlobalTheory.SnMass.NEntry.haarLie_entries <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselDoubleCosetMeasure_bigCell_eq : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μG μW μW' : Measure (Mt k r)) (c κ : ℝ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec → 0 < c → 0 < κ → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → IsHaarOn (UWset k r z') μW' → μW' Set.univ = 1 → AEMeasurable (fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) (volume.withDensity fun q => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)) ∧ IsDis (Greg k r z z') μG (muProd μW (haarLie (Nset k r) (ENNReal.ofReal κ))) (muProd μW' (haarLie (Nset k r) (ENNReal.ofReal κ))) (ENNReal.ofReal (c * 2 ^ (r + 1) * volUn k ^ 2 / volUn (k - 1) / (Tz k r z * Tz k r z') ^ k / κ ^ 2) • (volume.withDensity fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)).map fun q => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) := by
  first | exact @GlobalTheory.DoubleCosetMeasure.isDis_bigCell | exact GlobalTheory.DoubleCosetMeasure.isDis_bigCell | (intros; apply GlobalTheory.DoubleCosetMeasure.isDis_bigCell <;> assumption)
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.local_data_both_amplitude_sides : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) lam (A : LocS W), 0 < θ → 0 < D.host.v → HypTT D w w' → GoodW D τ w w' θ W → GoodS D lam A → IsURepOn (GG D.R.k D.R.rS) A.σ ∧ IsIrredOn (GG D.R.k D.R.rS) A.σ ∧ W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS ∧ OneSide W.z W.π (psiS D W.z) W.μG W.μW W.μN W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' W.μN W.νS' A.Φ' A.cN := by
  first | exact @GlobalTheory.Amp.Side.both_sides | exact GlobalTheory.Amp.Side.both_sides | (intros; apply GlobalTheory.Amp.Side.both_sides <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieri

variable {k r : ℕ}

def withRep (L : LocBessel k r) (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (hR : R.IsDS L.ε mu) :
    LocBessel k r :=
  { L with lam := mu, hlam := hR.1, Hs := R.H, hsN := R.nacg, hsI := R.ips, hsC := R.cs, σ := R.σ, hσ := hR.2 }

theorem fdegHC_pos {n : ℕ} {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < fdegHC lam := by
  unfold fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    exact sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)

def coefR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (R : Rep k r) (v v' : R.H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, R.σ g v'⟫_ℂ • ξ)

theorem amp_eq_orb (hH : Hyps) (hA : AmpKF) (hC : CellConv) (L : LocBessel k r) (R : Rep k r)
    (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H)
    [CompleteSpace L.Wp] [CompleteSpace L.Wq]
    (hR : R.IsDS L.ε mu) (hgap : GapAtLeast L.ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hcell : GapCell k r h)
    (hc : L.c ≠ 0) (hκ : L.κN ≠ ⊤) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hl : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    (hw : PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hD : CellData L μG γ μR νR ν) (v v' : R.H) (hv : R.KFin v) (hv' : R.KFin v')
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefR R v v' ξ ξ') γ) ν ∧
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) * (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ)) • amp R l l' w νR γ =
        OrbInt L (coefR R v v' ξ ξ') γ ν := by
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨-, -, -, -, hsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw
  have hle : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w, hwK, rfl⟩
  have hD' : CellData (withRep L R mu hR) μG γ μR νR ν := hD
  obtain ⟨b, hb0, hb1, hb2⟩ := hC k r L h μG γ μR νR ν hκ hok hcell hD hD.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hOne : OnePlaceKF (withRep L R mu hR) h μG w l l' :=
    ⟨⟨hgap, hok, hc, hw, hG, fun x hx y hy => hl x (hsm x (hle x hx)) y (hle y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hle y hy)⟩,
      fun x hx y hy => hl x (hsm x (hle x hx)) y (hKT y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hKT y hy)⟩
  have h1 := hA hH.1 k r (withRep L R mu hR) h μG w l l' hOne γ μR νR ν hD' b hb0 hb1 hb2 v v' hv hv' ξ ξ'
  have h2 := (GlobalTheory.T.cell_data_support hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD').2 b hb0 (by linarith)
    hb2 v v' hv hv' ξ ξ'
  refine ⟨h2, ?_⟩
  obtain ⟨c, hc0, hc1⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r L.ε μG hG
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hf : (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) ≠ 0 := by
    rw [(hc1 mu R hR).1 w hw0]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hc0 (fdegHC_pos hR.1.1)).ne'
  have h3 : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • amp R l l' w νR γ =
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)⁻¹) • OrbInt L (coefR R v v' ξ ξ') γ ν := h1
  rw [mul_smul, h3, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem herm_inv {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om : ι → ℂ} {a g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ GG k r) (hg : g ∈ GG k r) (hom : ρ a *ᵥ om = om) (x : ι → ℂ) :
    herm Γ (ρ (a⁻¹ * g) *ᵥ x) om = herm Γ (ρ g *ᵥ x) om := by
  obtain ⟨-, -, -, hmul, hinv, -⟩ := hρ
  obtain ⟨hai, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
  have hm : a⁻¹ * g ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg
  have e : ρ g = ρ a * ρ (a⁻¹ * g) := by
    rw [← hmul a ha _ hm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold herm
  rw [e]
  conv_rhs => rw [← hom]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hinv a ha]

theorem one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_Sset_of_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g ∈ Sset k r z := by
  refine ⟨g, hg, 1, ⟨one_mem_UH, fun a i _ => ?_, fun i j _ _ _ => ?_⟩, (Matrix.mul_one g).symm⟩ <;>
    exact Matrix.one_apply

theorem mem_Sset_of_N (z : Fin (2 * r + k + 1) → ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g ∈ Sset k r z :=
  ⟨1, ⟨one_mem_UH, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, g, hg,
    (Matrix.one_mul g).symm⟩

theorem herm_cell {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om om' : ι → ℂ} {z z' : Fin (2 * r + k + 1) → ℂ}
    (hom : ∀ g ∈ Sset k r z, ρ g *ᵥ om = om) (hom' : ∀ g ∈ Sset k r z', ρ g *ᵥ om' = om')
    {a n γ n' a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ GG k r)
    (ha : a ∈ UWset k r z) (hn : n ∈ Nset k r) (ha' : a' ∈ UWset k r z') (hn' : n' ∈ Nset k r) :
    a⁻¹ * n⁻¹ * γ * n' * a' ∈ GG k r ∧
      herm Γ (ρ (a⁻¹ * n⁻¹ * γ * n' * a') *ᵥ om') om = herm Γ (ρ γ *ᵥ om') om := by
  have mul : ∀ {x y}, x ∈ GG k r → y ∈ GG k r → x * y ∈ GG k r := fun hx hy => Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hx hy
  have hai := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha.1).1
  have hni := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hn.1).1
  have h1 := mul (mul hai hni) hγ
  have h2 := mul h1 hn'.1
  refine ⟨mul h2 ha'.1, ?_⟩
  rw [hρ.2.2.2.1 _ h2 _ ha'.1, hρ.2.2.2.1 _ h1 _ hn'.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hom' _ (mem_Sset_of_UW ha'), hom' _ (mem_Sset_of_N z' hn'), Matrix.mul_assoc,
    herm_inv hρ ha.1 (mul hni hγ) (hom _ (mem_Sset_of_UW ha)),
    herm_inv hρ hn.1 hγ (hom _ (mem_Sset_of_N z hn))]

theorem amp_pieri : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  intro hH hA hC k r ι κ _ _ _ _ ρ Γ d L R RI io pr ep mu muI h μG om om' l l' lI lI' w wI κ₀ κ₁
  haveI := FiniteDimensional.complete ℂ L.Wp
  haveI := FiniteDimensional.complete ℂ L.Wq
  intro hR hgap hRI hok hcell hc hκ hG hρ hT hom hom' hl hl' hlI ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hw hwI hκI γ μR νR ν hD
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  have hvs : v ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v hv
  have hvs' : v' ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v' hv'
  obtain ⟨hK, hsplit⟩ := GlobalTheory.KFinCoefSplit.kfin_coef_mul_split hKF k r ι κ ρ Γ d R RI io pr ep L.ε mu muI om om' v v' hR
    (fun I => (hRI I).1) hρ hT hv hv'
  obtain ⟨-, e0⟩ := amp_eq_orb hH hA hC L R mu h μG l l' w hR hgap hok hcell hc hκ hG hl hl' hw γ μR νR ν hD
    v v' hv hv' (l v) (l' v')
  have eI := fun I => amp_eq_orb hH hA hC L (RI I) (muI I) h μG (lI I) (lI' I) (wI I) (hRI I).1 (hRI I).2 hok hcell
    hc hκ hG (hlI I).1 (hlI I).2 (hwI I) γ μR νR ν hD _ _ (hK I).1 (hK I).2 (l v) (l' v')
  have hae := (GlobalTheory.T.cell_data_support hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD).1
  have hc0 : ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ ≠ 0 :=
    mul_ne_zero (inner_self_ne_zero.mpr hv0) (inner_self_ne_zero.mpr hv0')
  have horb : herm Γ (ρ γ *ᵥ om') om • OrbInt L (coefR R v v' (l v) (l' v')) γ ν =
      ∑ I, (ep I : ℂ) • OrbInt L (coefR (RI I) (∑ c, pr I c (tm R om v c)) (∑ c, pr I c (tm R om' v' c))
        (l v) (l' v')) γ ν := by
    unfold OrbInt
    simp only [← integral_smul]
    refine Eq.trans (integral_congr_ae ?_) (integral_finsetSum _ (fun I _ => (eI I).1.smul (ep I : ℂ)))
    filter_upwards [hae] with p hp
    obtain ⟨hm, he⟩ := herm_cell hρ hom hom' hD.1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs := hsplit _ hm
    rw [he] at hs
    ext x
    simp only [besselIntg, coefR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul, Pi.smul_apply,
      ← Finset.sum_smul]
    congr 1
    have key : ∀ (D A B C : ℂ) (e f : κ → ℂ), D * C = ∑ I, e I * f I →
        D * A * (B * C) = ∑ I, e I * A * (B * f I) := by
      intro D A B C e f hh
      rw [show D * A * (B * C) = D * C * (A * B) by ring, hh, Finset.sum_mul]
      exact Finset.sum_congr rfl fun I _ => by ring
    exact key _ _ _ _ _ _ hs
  apply smul_right_injective _ hc0
  simp only [Finset.smul_sum, smul_smul]
  rw [mul_comm, mul_assoc, mul_smul, e0, horb]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← (eI I).2, smul_smul, (hκI I v hvs).1, (hκI I v' hvs').2, inner_smul_left, inner_smul_right]
  congr 1
  simp only [RCLike.star_def]
  ring

end GlobalTheory.CellPieri

end
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitudes_relevant_cell_monomial_rep : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₀ : LocS W) (hA : GoodS D lam0 A₀) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'), 0 < θ → 0 < D.host.ka / gg D → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ' : ℝ, 0 < θ' → ∀ νR, RMeas D W γ θ' νR → ∃ (g₀ : MatKR D.R.k D.R.rS) (μR ν₀ : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)) (s : ℂ), CellData (toBessel D τ w w' θ W lam0 A₀ hW hA hT hT') W.μG g₀ μR ν₀ ν ∧ ν₀ {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 ∧ (∀ l, DminN W.z W.z' γ l = DminN W.z W.z' g₀ l) ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → A.J νR γ = s • A.J ν₀ g₀ := by
  first | exact @GlobalTheory.CellRed.amp_at_monomial | exact GlobalTheory.CellRed.amp_at_monomial | (intros; apply GlobalTheory.CellRed.amp_at_monomial <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.splitPlace_base_ne_of_distinct_type_primes : ∀ (D : D7) (s s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (kv kv' : Σ k : Fin 2, D.nd.PlG k), s.w = D.naut.plGw kv.1 kv.2 → s'.w = D.naut.plGw kv'.1 kv'.2 → kv ≠ kv' → s.v ≠ s'.v := by
  first | exact @GlobalTheory.SplitPlaceDistinct.splitPlace_v_ne | exact GlobalTheory.SplitPlaceDistinct.splitPlace_v_ne | (intros; apply GlobalTheory.SplitPlaceDistinct.splitPlace_v_ne <;> assumption)
end

section


theorem _root_.GlobalTheory.T.integralUnipotent_covolume_finite_bounded : GlobalTheory.TypeAsm.CovNC := by
  first | exact @GlobalTheory.TypeAsm.covNC_holds | exact GlobalTheory.TypeAsm.covNC_holds | (intros; apply GlobalTheory.TypeAsm.covNC_holds <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frame_adelicColumnLattice_linked_reference : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ Fr : FrQ D wt, FrLink X u wt ιA Fr := by
  first | exact @GlobalTheory.St.G.FrameLink.frame_exists | exact GlobalTheory.St.G.FrameLink.frame_exists | (intros; apply GlobalTheory.St.G.FrameLink.frame_exists <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nonGeneric_generic_terms_closed_under_localUnitary : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → LocClosed F F' Z FP (Y.tO u u').ngSet ∧ LocClosed F F' Z FP (Y.tO u u').genSet ∧ (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ ∀ t ∈ (Y.tO u u').genSet, t.G ≠ 0 := by
  first | exact @GlobalTheory.LocOrbit.closed_ng_gen | exact GlobalTheory.LocOrbit.closed_ng_gen | (intros; apply GlobalTheory.LocOrbit.closed_ng_gen <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.globalInnerDatum_eq_iff_local_data_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (gdat F F' Λ₁ = gdat F F' Λ₂ ↔ y₁ = y₂) := by
  first | exact @GlobalTheory.Unfold.InnerDict.gdat_eq_iff | exact GlobalTheory.Unfold.InnerDict.gdat_eq_iff | (intros; apply GlobalTheory.Unfold.InnerDict.gdat_eq_iff <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.same_row_doubleCoset_inner_data_one_rational_class : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t t' : TauC Y u u') (Λ₁ Λ₂ : LV D), TG F F' t Λ₁ → TG F F' t' Λ₂ → key t = key t' → LRel F F' Λ₁ Λ₂ := by
  first | exact @GlobalTheory.KeyRel.same_key_lrel | exact GlobalTheory.KeyRel.same_key_lrel | (intros; apply GlobalTheory.KeyRel.same_key_lrel <;> assumption)
end
