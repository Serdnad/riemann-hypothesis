module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermsSameDoubleCosetSameLocalData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle441
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle417
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle348
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle406
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CovolIdx
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle056
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle333
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle415
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle420
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle435
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle101
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.global_terms_same_doubleCoset_same_local_data : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → ∀ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ m ∈ Formalism.L2.SG.NGData.NRat F₁, Formalism.HermitianLatticesTheory.gmap (n * m) Λ = Λ → (∀ a, frame F₂ a = (n * m) (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ (n * m) (gS D) → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  first | exact @GlobalTheory.LocSame.over_same | exact GlobalTheory.LocSame.over_same | (intros; apply GlobalTheory.LocSame.over_same <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  first | exact @GlobalTheory.LabPinTop.labTie_of_series | exact GlobalTheory.LabPinTop.labTie_of_series | (intros; apply GlobalTheory.LabPinTop.labTie_of_series <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  first | exact @GlobalTheory.UnifPTGap.uniformPT_gap | exact GlobalTheory.UnifPTGap.uniformPT_gap | (intros; apply GlobalTheory.UnifPTGap.uniformPT_gap <;> assumption)
end

section

open Formalism.L2.SG.Pf.MainEqSteps

theorem _root_.GlobalTheory.T.normalCount_genericRow : StepNormalsG := by
  first | exact @GlobalTheory.stepNormalsG_holds | exact GlobalTheory.stepNormalsG_holds | (intros; apply GlobalTheory.stepNormalsG_holds <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovMass

variable {D : D7} (X : HidaSetting D)

noncomputable def realPt (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : X.B.I.Ginf :=
  (Classical.choose ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1

theorem realPt_spec {γ : Formalism.HermitianLatticesTheory.isom (VS D).hT} {x : X.B.I.GA} (h : RatLink X x γ.1) : realPt X γ = x.1 := by
  have hs := Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)
  unfold realPt
  rw [hs.2 x h]

theorem realPt_link (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : ∃ x : X.B.I.GA, RatLink X x γ.1 ∧ realPt X γ = x.1 :=
  ⟨_, (Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1, rfl⟩

noncomputable def realPtHom : Formalism.HermitianLatticesTheory.isom (VS D).hT →* X.B.I.Ginf where
  toFun := realPt X
  map_one' := by
    obtain ⟨x, hx, e⟩ := realPt_link X 1
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x x _ _ hx hx)
    have h2 := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x (x⁻¹) _ _ hx h.2.1).1
    have h3 : RatLink X (x * x⁻¹) (1 : Formalism.HermitianLatticesTheory.isom (VS D).hT).1 := by simpa using h2
    rw [realPt_spec X h3]; simp
  map_mul' := by
    intro γ δ
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    obtain ⟨y, hy, ey⟩ := realPt_link X δ
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).1
    rw [realPt_spec X (γ := γ * δ) h, ex, ey]; rfl

theorem realPtHom_injective : Function.Injective (realPtHom X) := by
  intro γ δ h
  obtain ⟨x, hx, ex⟩ := realPt_link X γ
  obtain ⟨y, hy, ey⟩ := realPt_link X δ
  have h' : x.1 = y.1 := by rw [← ex, ← ey]; exact h
  exact Subtype.ext (((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).2.2 h')

theorem realPts_eq_map (H : Subgroup ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (hH : H ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    realPts X (H : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = ((H.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (realPtHom X) : Set X.B.I.Ginf) := by
  ext y
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨⟨n, hH hn⟩, hn, realPt_spec X (γ := ⟨n, hH hn⟩) hx⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    exact ⟨x, γ.1, hx, ex, hγ⟩

theorem realPts_countable (S : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) : (realPts X S).Countable := by
  have := Formalism.L2.SG.TermOp.Vanish.countable_nf X.B.I.E
  have hsub : realPts X S ⊆ ⋃ M : Fin X.B.I.n → Fin X.B.I.n → X.B.I.E,
      {y : X.B.I.Ginf | ∀ v, uMat (y v) = (X.B.I.P v)⁻¹ * (Matrix.of M).map (X.B.I.φ v) * X.B.I.P v} := by
    rintro _ ⟨x, n, ⟨M, -, h1, -⟩, rfl, -⟩
    exact Set.mem_iUnion.2 ⟨fun i j => (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) i j, h1⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun M => Set.Subsingleton.countable ?_)
  intro y hy y' hy'
  funext v
  exact Subtype.ext (Units.ext ((hy v).trans (hy' v).symm))

end GlobalTheory.CovMass

theorem GlobalTheory.CovMass.covol_eq_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∀ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ ROinf t₀ ∧ s * y ∈ K) → (μR K).toReal = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat ρ t₀.lam) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin K hK
  obtain ⟨hKm, hKu⟩ := hK
  have hlink := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hgrp := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).1
  obtain ⟨KA, ⟨hKAm, hKAu⟩, hKA⟩ :=
    GlobalTheory.T.covolume_integralStabiliser_normalisedHaar D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin
  have hRO := GlobalTheory.T.realPoints_termAutomorphisms_eq_movedStabilizer D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hfin1, hfin2⟩ := GlobalTheory.T.latticeStabiliser_commensurable_integralPoints (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ _ G hk (c.lat ρ t₀.lam) (by first | exact GlobalTheory.HL.ProdStruct.full_lattice_of_term G hterm | exact hterm.1)

  let cj : ((VS D).V ≃ₗ[D.host.E] (VS D).V) →* G.GLV :=
    { toFun := c.grp ρ
      map_one' := by ext x; simp [GlobalTheory.HL.GCoord.grp]
      map_mul' := by intro m n; ext x; simp [GlobalTheory.HL.GCoord.grp] }
  have hcj : ∀ n, cj n = c.grp ρ n := fun _ => rfl
  have hcjs : Function.Surjective cj := fun x => hgrp.2.2.2.1 ρ x
  have hconj : ∀ n, c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * n * t₀.lin) = c.grp ρ n := by
    intro n
    have h1 : ∀ y, t₀.lin (t₀.lin⁻¹ y) = y := fun y => by
      show (t₀.lin * t₀.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    have h2 : ∀ z, t₀.lin ((ρ * t₀.lin).symm z) = ρ.symm z := fun z => by
      rw [LinearEquiv.eq_symm_apply]; exact (ρ * t₀.lin).apply_symm_apply z
    ext x
    simp only [GlobalTheory.HL.GCoord.grp, LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_trans_apply, h1, h2]

  have hStN : ∀ g, g ∈ G.St → g ∈ G.N := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').1, he⟩
  have hStN' : ∀ g, g ∈ G.St → g ∈ G.N' := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').2, he⟩
  have hK0St : G.K0 ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1.1, he⟩
  have hLSt : G.stabL (c.lat ρ t₀.lam) ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1, he⟩
  have hStI : G.St.comap cj ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn =>
    ((hgrp.1 n).2 (hStN _ hn)).1
  set P := G.K0.comap cj with hP
  set Q := (G.stabL (c.lat ρ t₀.lam)).comap cj with hQ
  have hPI : P ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hK0St hn)
  have hQI : Q ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hLSt hn)
  set A := (P.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hA
  set B := (Q.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hB
  have hAset : (A : Set X.B.I.Ginf) = realPts X {σ | c.grp ρ σ ∈ G.K0} :=
    (GlobalTheory.CovMass.realPts_eq_map X P hPI).symm
  have hBset : (B : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.ROinf t₀ := by
    rw [hRO]; exact (GlobalTheory.CovMass.realPts_eq_map X Q hQI).symm
  have hAmem : ∀ y, y ∈ A ↔ y ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} := fun y => by
    rw [← hAset]; rfl
  have hBmem : ∀ y, y ∈ B ↔ y ∈ Formalism.L2.SG.TermOp.ROinf t₀ := fun y => by
    rw [← hBset]; rfl

  obtain ⟨γw, s, s', μw, hγw, hs, hs', hdec, hμwH, hμwS, hμR⟩ := hPin
  have hH := Formalism.L2.SG.Pf.VolPinAsm.pinned_haar t₀ w γw s s' μw hs hs' hdec hμwH
  rw [← hμR] at hH
  have hAR : ∀ y ∈ A, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
    intro y hy
    obtain ⟨x, n, hx, rfl, hn⟩ := (hAmem y).1 hy
    have hnS : c.grp ρ n ∈ G.St := hK0St hn
    refine ⟨((hlink.2.2 u x n hx).1).1 ((hgrp.1 n).2 (hStN _ hnS)), ?_⟩
    have hm : t₀.lin⁻¹ * n * t₀.lin ∈ NRat (lf D (X.Fu u')) :=
      (hgrp.2.1 _).2 (by rw [hconj]; exact hStN' _ hnS)
    have hl : RatLink X (t₀.pt⁻¹ * x * t₀.pt) (t₀.lin⁻¹ * n * t₀.lin) :=
      (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ t₀.rep.2.1 t₀.rep.2.1).2.1 hx).1 t₀.rep.2.1).1
    have h2 := ((hlink.2.2 u' _ _ hl).1).1 hm
    simpa [Prod.fst_mul, Prod.fst_inv] using h2
  have hBR : ∀ y ∈ B, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := fun y hy =>
    Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset t₀ ((hBmem y).1 hy)
  haveI hCA : Countable A := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.K0}).to_subtype
    rw [← hAset] at this; exact this
  haveI hCB : Countable B := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)}).to_subtype
    rw [← hRO, ← hBset] at this; exact this

  have hiA : B.relIndex A = (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hPI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hiB : A.relIndex B = G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hQI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hcov := Formalism.L2.SG.Pf.CovolIdx.covol_commens μR (Formalism.L2.SG.TermOp.Vanish.Rset t₀) hH.2.2.1 A B
    (fun x hx => hH.2.2.2 x (hAR x hx)) (fun x hx => hH.2.2.2 x (hBR x hx))
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hAR x hx) hy)
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hBR x hx) hy) KA K hKAm hKm
    (fun y hy => by simpa only [hAmem] using hKAu y hy) (fun y hy => by simpa only [hBmem] using hKu y hy)
    (by rw [hiA]; exact hfin1) (by rw [hiB]; exact hfin2)
  rw [hiA, hiB, hKA] at hcov
  set a := (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 with ha
  set b := G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) with hb
  set gi : ℝ := ((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹ with hgi
  have hgi0 : 0 ≤ gi := by rw [hgi]; positivity
  have hbne : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hfin2
  have hKeq : μR K = ENNReal.ofReal gi * (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
    rw [hcov, ENNReal.mul_div_cancel_right hbne (by simp)]
  rw [hKeq, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hgi0]
  simp only [ENNReal.toReal_natCast]
  unfold GlobalTheory.HL.GFrames.mu GlobalTheory.HL.invVol
  rw [← ha, ← hb]
  ring
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpLoc

theorem hsNormSq_amp_loc : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  intro D X Y hF hI C hB u u' t s hs hG hr hGap τ μ ν hμ hq hroot
  have hW : ∀ τ', GoodW D τ' u u' 1 (locW C u u' τ') := fun τ' =>
    goodW_of C u u' τ' (Formalism.L2.SG.Pf.colsTypeTr C u τ') (Formalism.L2.SG.Pf.colsTypeTr C u' τ')
      (Formalism.L2.SG.Pf.zTr C u τ') (Formalism.L2.SG.Pf.zTr C u' τ') (Formalism.L2.SG.Pf.haarTr C τ')
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u' τ (s.pt.1 (vOf X τ)) ν
  have hR2 : RMeas D (locW C u u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) 1
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ)))) := by
    obtain ⟨p, hp⟩ := hroot
    refine ⟨p, _, hp, ?_⟩
    rw [ENNReal.ofReal_one, one_smul]
    exact GlobalTheory.T.quotientMeasure_besselModel_of_local_quotient D X 1 C τ (s.pt.1 (vOf X τ)) μ ν hμ hq
  obtain ⟨a, ha, a', ha', hga⟩ := GlobalTheory.T.real_point_term_and_lift_same_real_double_coset D X Y hF hI 1 C u u' t s hs τ
  have hR4 : RMeas D (locW C u u' τ) (gamR hI C t τ) 1 (nu1 hI C t τ) := by
    have h := GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u' hW t hG hr τ
    unfold nu1
    rw [dite_eq_left h]
    exact h.choose_spec
  obtain ⟨p0, hp0⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨hΦ, hΦ', hc, hc'⟩ := GlobalTheory.T.localRealData_functions_equivariant_continuous D X 1 C hB u u' τ hGap
  have h5 := GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant D τ u u' 1 (locW C u u' τ) (locS hB u u' τ) (hW τ)
    (Nat.cast_pos.2 (D.mem u).A.T_prime.pos) (Nat.cast_pos.2 (D.mem u').A.T_prime.pos) hΦ hΦ' hc hc'
    (gamR hI C t τ) a a' p0 (nu1 hI C t τ) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ))))
    hp0 ha ha' hR4 (by rw [← hga]; exact hR2)
  rw [← h5, ← hga, e1]
  exact Formalism.L2.SG.LoopTerm.hsNormSq_smul _ _

end GlobalTheory.AmpLoc
end

section

namespace GlobalTheory.St

theorem stepChoiceDataC_of_siegelWeil_inInfinity :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
    (∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word),
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.RealObj.InInfinityX X u u' 1) →
    Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC :=
  fun h hI => Formalism.L2.SG.Pf.choice_massData (GlobalTheory.St.swxs_of_siegelWeil h)
    Formalism.L2.SG.Pf.ProdConvCut2.prodConv_onTied hI

end GlobalTheory.St
end
