module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ZpowNeOneOfClose
public import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpCritPOf
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
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
import Mathlib.Tactic.ENatToNat
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
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LMemMaxOL
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseA

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA\nimport Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd\npublic import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ZpowNeOneOfClose\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Classical

namespace GlobalTheory.LevelClauseOdd

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem exists_point_over_letter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL)
    (c : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hA.2.2 c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hA.2.2).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hA.2.2).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := Formalism.MainNotions.UnusedSlot80.LevR.trans_prim (D.loc l) ((HW l).W K 1 LL hA.2.2)
    (Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA) hζ₁ _ hβ
  have hmem : ∀ y, ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val) y ∈ LL.1 :=
    hA.2.2.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hA.2.2.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    have hgx : (g : GQ l) (x : Om l) = x :=
      (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).mp g.2 _
        ((inf_le_left : K0 K ≤ K.1) x.2)
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

theorem clause_at_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL) :
    Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hA.2.2) := by
  have tie := ((Cm l).C K 1 LL hA.2.2).tie
  have hs := (HW l).W_s K 1 LL hA.2.2
  have hp : ((((D.loc l).PD K).p : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have hv := ((HW l).W K 1 LL hA.2.2).v_l
    rw [h, AddValuation.map_zero] at hv
    exact WithTop.top_ne_one hv
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun x => ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  refine Formalism.MainNotions.UnusedSlot80.LevR.level_condition_of_level_zero _ ((Cm l).C K 1 LL hA.2.2).tie.levB hs
    ((Cm l).C K 1 LL hA.2.2).tie.levN_eq ((Cm l).C K 1 LL hA.2.2).tie.levB_φ hp ?_
  intro T hT c ζ hζ
  have hζl : IsPrimitiveRoot ζ l := by rwa [(D.loc l).PD_p] at hζ
  obtain ⟨τ, hτ⟩ := exists_point_over_letter D HW F h9 l K LL hA c ζ hζl
  have hover : ∀ x : ↥(K0 K), τ (algebraMap ↥(K0 K) ↥K.1 x) = ((HW l).W K 1 LL hA.2.2).emb c x := by
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have h4' := ((h4 l K 1 LL hA.2.2 T hT).2 c ζ τ hτ).2
  exact Formalism.MainNotions.UnusedSlot80.LevR.lev0 _ T c ζ τ (Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le _ T c τ hover hsurj) h4'



theorem torsion_transitive (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL) :
    Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans ((HW l).W K 1 LL hA.2.2) := by
  exact _root_.Formalism.MainNotions.N.Pv.LocalLengthBound.ptTrans_of_caseA D HW F h9 l K LL hA

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans ((HW l).W K 1 LL hA.2.2) :=
  fun D HW F Cm h4 h9 l _ K LL hA =>
    ⟨clause_at_levels D HW F Cm h4 h9 l K LL hA, torsion_transitive D HW F h9 l K LL hA⟩

end GlobalTheory.LevelClauseOdd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseA =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseA", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified\nimport Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition\nimport Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf\npublic import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower\npublic import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL\npublic import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpCritPOf\npublic import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe\nimport Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LMemMaxOL\nimport Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem\nimport Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.ExpansionsOdd



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm hN l _ K LL hA
  obtain ⟨p1, -, p3, p4, p5, -, -, -, p9, -⟩ := hN
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.OLC.complete_max LL
  have hLT := GlobalTheory.LevelClauseOdd.main D HW F Cm p4 p9 l K LL hA
  have C := ((Cm l).C K 1 LL hA.2.2).tie
  have hs : ((HW l).W K 1 LL hA.2.2).s = 1 := (HW l).W_s K 1 LL hA.2.2
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie _ hs C
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) := p9 l K 1 LL hA.2.2
  refine ⟨fun hCA => ?_, Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of _ hLT.1 hG.1 hG.2, ?_⟩
  · have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA.2.2) :=
      (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA.2.2))) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA.1)).1
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of _ hring hCA
  · have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
      rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
    have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL
    have hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hA.2.2) := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ h9
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL)
      (p1 l K 1 LL hA.2.2) (p3 l K 1 LL hA.2.2) hLT.1 (p5 l K 1 LL hA.2.2) h9 hD hB C
      (p4 l K 1 LL hA.2.2) hLT.2

end GlobalTheory.ExpansionsOdd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseA =====
