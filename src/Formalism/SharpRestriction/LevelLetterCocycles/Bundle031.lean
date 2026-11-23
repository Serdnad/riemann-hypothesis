module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerSmulOfLevelOne
import Formalism.SharpRestriction.LevelLetterCocycles.HermFlagUnipotentAnisotropicVectorSubMem
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfExactnessAndData
public import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow
public import Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame
public import Formalism.SharpRestriction.LevelLetterCocycles.LamZero
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle029
import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
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
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle028

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem truncation_clause_of_lattice_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h8 : Formalism.MainNotions.CrystallineLiftingInputs.adm8 D HW F) (h9 : Formalism.MainNotions.CrystallineLiftingInputs.adm9 D HW F) :
    Formalism.MainNotions.CrystallineLiftingInputs.adm15 D HW F Cm := by
  refine ⟨Formalism.MainNotions.CrystallineLiftingInputs.TToolAlg_holds, fun l _ K LL hg _ => ?_⟩
  have hP9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := hP9 l K 1 LL hg
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  exact ⟨tTool1_of _ hinj hO2 hP9W (h8 l K 1 LL hg),
    tTool2_of _ hinj hO2 hlm hP9W (h8 l K 1 LL hg) (h9 l K 1 LL hg)⟩

theorem tTool2Z_DU (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h8 : Formalism.MainNotions.CrystallineLiftingInputs.adm8 D HW F) (h9 : Formalism.MainNotions.CrystallineLiftingInputs.adm9 D HW F) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hP9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := hP9 l K 1 LL hg
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  exact tTool2Z_of _ hinj hO2 hlm hP9W (h8 l K 1 LL hg) (h9 l K 1 LL hg)

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData
end
end

section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem ddExactL_of_litFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : Split.DDExactL D HW := by
  intro l _ K LL hG hCA _ T₂ Y ι π _ _ hses
  obtain ⟨hinj, -, hker⟩ := (h l K LL hCA).2.1 T₂ Y _ ι π hses
  refine ⟨fun x => (hker _).2 ⟨x, rfl⟩, fun x hx => hinj (by rw [hx, map_zero]), fun u hu => (hker u).1 hu⟩

theorem splitting_of_literature_exactness (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmSplitA D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hS : Split.SplitShapeL D HW) : SplittingArcLifting D HW F Cm :=
  splitting_general_of_exactness D HW F Cm hA h6 hH hTr hWX (ddExactL_of_litFont D HW F hFont) hS

end Formalism.MainNotions.UnusedSlot80
end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def at0Hom (W : LocWach PD LL O v n) (hz : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries O →+* LetA O n where
  toFun := Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W
  map_one' := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C W (1 : O)
    rw [map_one, map_one] at this
    exact this
  map_mul' := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_mul W hz
  map_zero' := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C W (0 : O)
    rw [map_zero, map_zero] at this
    exact this
  map_add' := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evaluation_add W hz

theorem at0Hom_apply (W : LocWach PD LL O v n) (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f : PowerSeries O) :
    at0Hom W hz f = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := rfl

theorem gCoord_holds (W : LocWach PD LL O v n) : GCoordProp W := by
  intro T i h c r e e' he P Z hP hz hqpu k hg hgDL a ha l
  classical
  have hqp : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = Formalism.MainNotions.LiftingTheory.qp W := by
    rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evaluation_add W hz, Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_X_eq_pi0 W hz, Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C, map_natCast]
    rfl
  set x := Formalism.MainNotions.LiftingTheory.qp W ^ c • Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k with hx
  have hxN : x ∈ W.N T := (W.N T).smul_mem _ hg
  have hxDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := by
    refine ⟨by rw [hx, smul_comm, hgDL.1], fun δ hδ => ?_⟩
    rw [hx, Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA, map_pow,
      Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.qp_mem W (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) δ hδ, hgDL.2 δ hδ]

  have e1 : x = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) • e l := by
    rw [hx, ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    rw [show Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) =
      at0Hom W hz ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) from rfl, map_mul, map_pow,
      at0Hom_apply, at0Hom_apply, hqp]

  have hcancel : x = Formalism.MainNotions.LiftingTheory.qp W ^ h • Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.ftE W T e' Z k := by
    rw [hx, Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE, ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow,
      ← mul_pow, Ring.mul_inverse_cancel _ hqpu, one_pow, one_smul]
  have e2 : x = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((P * Z) l k) • e l := by
    rw [hcancel, Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.ftE, Finset.smul_sum]
    simp only [pow_one]
    have : ∀ m₁, Formalism.MainNotions.LiftingTheory.qp W ^ h • (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Z m₁ k) • W.φD T (e' m₁)) =
        ∑ l, (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Z m₁ k) * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (P l m₁)) • e l := by
      intro m₁
      rw [smul_comm, hP m₁, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_

    rw [← Finset.sum_smul, Matrix.mul_apply, ← at0Hom_apply W hz, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [map_mul, at0Hom_apply, at0Hom_apply, mul_comm]
  have huniq := (he.2 x hxN hxDL).unique e1.symm.symm e2
  exact congrFun huniq l

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

structure Ctx : Prop where
  hbij : Function.Bijective (algebraMap K₀ K)
  hs : W.s = 1
  hp2 : PD.p ≠ 2
  h5p : 5 ≤ PD.p
  hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W
  h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h
  h3 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p3 W T
  hmod : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀
  hΔ : IsUnit ((W.DelF.card : ℕ) : O)
  hsat : SATcore W
  hsatP : SATPcore W
  hTr : Formalism.MainNotions.LiftingTheory.coreTr W
  hH : Formalism.MainNotions.LiftingTheory.coreH W
  hinj : Function.Injective (algebraMap O LL)
  hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x
  hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v
  hp0 : ((PD.p : ℕ) : O) ≠ 0

variable {W}

theorem Ctx.hCA (C : Ctx W) : Formalism.MainNotions.LiftingTheory.CaseA W := ⟨C.hbij, C.hs, C.hp2⟩

theorem exists_smul_pow_eq_sum_of_inFNc (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (N₁ : ℕ) (hN₁ : Hw A.G₀ A.S A.η (A.ty (a + 1)) ≤ N₁) (x : W.DD T) (hx : InFNc W T (a + 1) 1 x) :
    ∃ (r : ℕ) (bb : Fin r → W.DD T) (β : Fin r → LetA O n), (∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a (bb j)) ∧
      (∀ j, β j ∈ W.AΔ) ∧ ps W 0 ^ N₁ • x = ∑ j, β j • W.φD T (bb j) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y, hyN, hya, rfl⟩ := hx
  rw [one_smul]
  have hyl : y ∈ W.Nl T (a + 1) := ⟨y, hyN.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hya⟩
  have h1 := Formalism.MainNotions.UnusedSlot80.ArcC.iter_down W C.hs T h5T (a + 1) 1 y hyl
  rw [Finset.prod_range_one, pow_zero, AlgHom.one_apply, Nat.cast_zero, sub_zero, Nat.cast_one,
    add_sub_cancel_right] at h1
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hN₁
  have e1 : ps W 0 ^ N₁ • y = (w' ^ N₁ * W.q ^ dd) • (W.q ^ Hw A.G₀ A.S A.η (A.ty (a + 1)) • y) := by
    rw [hp0w, smul_smul, hdd]; congr 1; ring
  have h2 := Submodule.smul_mem _ (w' ^ N₁ * W.q ^ dd) h1
  rw [← e1] at h2
  obtain ⟨⟨r, bb0, hb0, huniq, -⟩, -⟩ := C.hmod T hT.1
  have h3 := Formalism.MainNotions.UnusedSlot80.ArcC.span_pow_le W T bb0 (fun z hz => (huniq z hz).exists) a 1 h2
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h3
  have hbΔ : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a ((letE a : LetA O n) • bb0 j) := fun j =>
    ⟨Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (hb0 j),
      ⟨bb0 j, (hb0 j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩
  have hp0Δ : ps W 0 ^ N₁ ∈ W.AΔ := W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) N₁
  obtain ⟨dd, hd, hzd⟩ := Formalism.MainNotions.WachCoordinates.Br.average C.hΔ cc
    (fun j => (W.φD T ^ 1 : Module.End O (W.DD T)) ((letE a : LetA O n) • bb0 j))
    (fun j δ hδ => φD_pow_Δ W T (hbΔ j).1.2 1 δ hδ)
    (fun δ hδ => (Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T hp0Δ hyN).2 δ hδ) hcc.symm
  refine ⟨r, fun j => (letE a : LetA O n) • bb0 j, dd, hbΔ, hd, ?_⟩
  rw [hzd]
  simp only [pow_one]

theorem up1 (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (H : ℕ) (hH : Mw A.G₀ A.S A.η (A.ty (a + 1)) ≤ H) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFNc W T a 1 y) : InFNc W T (a + 1) 1 ((ps W 0 ^ H * vv) • W.φD T y) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y', hy'N, hy'l, rfl⟩ := hy
  rw [one_smul]
  have hQ : W.Q = W.q := by simp [LocWach.Q, C.hs]
  have hyl : y' ∈ W.Nl T (a + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨y', hy'N.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hy'l⟩
  have hM := h5T.1 (a + 1) y' hyl
  rw [hQ] at hM
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  have hN : (ps W 0 ^ H * vv) • W.φD T y' ∈ W.N T := by
    obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hH
    have e1 : (ps W 0 ^ H * vv) • W.φD T y' = (w' ^ H * W.q ^ dd * vv) •
        (W.q ^ Mw A.G₀ A.S A.η (A.ty (a + 1)) • W.φD T y') := by
      rw [hp0w, smul_smul]; congr 1; rw [hdd]; ring
    rw [e1]
    exact (W.N T).smul_mem _ hM
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((ps W 0 ^ H * vv) • W.φD T y') = (ps W 0 ^ H * vv) • W.φD T y' := by
    intro δ hδ
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', (W.AΔ.mul_mem (W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) H) hv) δ hδ,
      ← W.φγ_comm, hy'N.2 δ hδ]
  refine ⟨_, ⟨hN, hΔ⟩, ?_, by rw [one_smul]⟩
  rw [smul_comm]
  congr 1
  have := φD_pow_letter W T a y' hy'l 1
  simpa using this

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers Formalism.MainNotions.UnusedSlot80.LevC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O]

def IntA (a : ZMod n) (g : W.EE) : Prop := ∃ u ∈ W.AΔ, g = algebraMap (LetA O n) W.EE (letE a * u)

theorem secOfP_int (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (x : W.DD T)
    (hx : InFP W T c' e 1 x) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol
      (lA W ^ κ • x) f ∧ ∀ k, IntA W (c' + (e : ZMod n)) (f k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨yP, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨β₀, hβ₀, hyβ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 yP hyP
  have hbl : ∀ m, (letE c' : LetA O n) • b m = b m := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1.1 m).2
  have hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m) :=
    fun m => φD_pow_letter W T c' (b m) (hbl m) e
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  let β : Fin d → LetA O n := fun m => letE (c' + (e : ZMod n)) * β₀ m
  have hβ : ∀ m, β m ∈ W.AΔ := fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hβ₀ m)
  have hΛx : x = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
    rw [hyx, hyβ]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [β, mul_smul]
    rw [smul_comm, hφl]
  have hHc := hH hCA T hTc c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  set M : ℕ := A.M PD.p with hMdef
  let κ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  set D : LetA O n := W.π₀ * Λ ^ 2 with hDdef
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA (c' + (e : ZMod n)) e
  have hYM' : Y ^ M = D * ν := by rw [hYdef, hMdef, hYM]
  choose ρ hρ using fun m m' =>
    Formalism.MainNotions.UnusedSlot80.ArcF.frame_inv_poly hinj sol (fun k => (hb.2 k).2) M κ yy hyy zz hzz Y m m'
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  let GY : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m') * Y ^ r
  have hGY : ∀ k m', GY k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  let aa : Fin d → LetA O n := fun k => ∑ m', GY k m' * β m'
  have haa : ∀ k, aa k ∈ W.AΔ := fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hGY k m') (hβ m')
  have haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k := by
    intro k
    simp only [aa, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [β]
    linear_combination (GY k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))
  let w : Fin d → LetA O n := fun m => -(ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m')
  have hw : ∀ m, w m ∈ W.AΔ := fun m => W.AΔ.neg_mem (W.AΔ.mul_mem hν (W.AΔ.sum_mem fun m' _ =>
      W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _) (hβ m')))
  have hkey : ∀ m, lA W ^ κ * lA W ^ κ * β m - ∑ k, aa k * HY m k = D * w m := by
    intro m
    have A2 : ∑ k, aa k * HY m k = ∑ m', (∑ k, HY m k * GY k m') * β m' := by
      simp only [aa, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∀ m', (∑ k, HY m k * GY k m') * β m' =
        lA W ^ κ * lA W ^ κ * ((if m = m' then 1 else 0) * β m') +
          Y ^ M * (Polynomial.aeval Y (ρ m m') * β m') := by
      intro m'
      have := hρ m m'
      simp only [HY, GY] at this ⊢
      rw [this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
      unfold lA
      split_ifs <;> ring
    rw [A2, Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, w]
    rw [hYM']
    ring
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1 s) _
  refine ⟨κ, fun k => algebraMap (LetA O n) W.EE (aa k),
    ⟨κ, 0, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), fun k => Λ * aa k,
      fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨W.AΔ.mul_mem hΛm (haa k), by rw [map_mul]⟩, ?_⟩,
    fun k => ⟨aa k, haa k, by
      show algebraMap (LetA O n) W.EE (aa k) = _
      congr 1
      conv_rhs => rw [← mul_one (letE (c' + (e : ZMod n)) : LetA O n), haal k]⟩⟩
  have hsum : ∑ k, aa k • ((W.φD T) ^ e)
      (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    congr 1
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hfin0 : lA W ^ κ • lA W ^ κ • x - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      D • ∑ m, w m • ((W.φD T) ^ e) (b m) := by
    rw [hsum, hΛx]
    simp only [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [smul_smul]
    rw [← sub_smul, ← hkey m]
    congr 1
    ring
  have hfin : lA W ^ 0 • (lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, (Λ * aa k) • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
      D • ∑ m, (Λ * w m) • ((W.φD T) ^ e) (b m) := by
    have e2 : lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, (Λ * aa k) • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
        Λ • (lA W ^ κ • lA W ^ κ • x - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) := by
      rw [smul_sub, Finset.smul_sum]
      simp only [mul_smul]
      rw [smul_comm Λ (lA W ^ κ) (lA W ^ κ • x)]
    rw [pow_zero, one_smul, e2, hfin0, smul_comm Λ D, Finset.smul_sum]
    simp only [mul_smul]
  rw [hfin]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (W.AΔ.mul_mem hΛm (hw m)) (hb.1.1 m))

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end
