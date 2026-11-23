module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle278
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel


theorem _root_.GlobalTheory.T.hasCompactSupport_finprod_schwartzBruhat_finiteAdeles : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod | exact GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod | (intros; apply GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel


theorem _root_.GlobalTheory.T.isLocallyConstant_finprod_schwartzBruhat_finiteAdeles : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.WeilM.isLocallyConstant_finprod_evalV | exact GlobalTheory.WeilM.isLocallyConstant_finprod_evalV | (intros; apply GlobalTheory.WeilM.isLocallyConstant_finprod_evalV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.schwartzBruhat_matrices_invariant_supported_eq_smul : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {m k : ℕ}
    (S : AddSubgroup (Matrix (Fin m) (Fin k) (Fv F v))) (B : Set (Matrix (Fin m) (Fin k) (Fv F v)))
    (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : Matrix (Fin m) (Fin k) (Fv F v) → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB _) (hf0 : f ≠ 0)
    (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin k) (Fv F v)), (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) →
      ∃ c : ℂ, g = c • f),
    ∃ c : ℂ, f = c • (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))).indicator 1 ∧
      IsOpen (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) ∧ IsCompact (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) := by
  first | exact @GlobalTheory.SBClosure.main | exact GlobalTheory.SBClosure.main | (intros; apply GlobalTheory.SBClosure.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : κ → AF F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun y => Φ (y + c)) ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.SchwartzTranslation.schA_add_const | exact GlobalTheory.SchwartzTranslation.schA_add_const | (intros; apply GlobalTheory.SchwartzTranslation.schA_add_const <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.AdelicCoordSB

theorem finprod_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ φ hSB hae
  classical
  refine ⟨?_, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hae⟩
  let L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → v.adicCompletion F) :=
    fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
  let S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := {v | ¬ φ v = Set.indicator (L v) 1}
  have hS : S.Finite := Filter.eventually_cofinite.1 hae
  let ev : (κ → FiniteAdeleRing (𝓞 F) F) → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) :=
    fun y v i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)
  have hev : ∀ y v i, ev y v i = (y i).1 v := fun _ _ _ => rfl
  have hcont : ∀ v, Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => ev y v := fun v =>
    continuous_pi fun i => (RestrictedProduct.continuous_eval (R := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      w.adicCompletion F) (A := fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp
      (continuous_apply i)
  have hfin : ∀ y, (Function.mulSupport fun v => φ v (ev y v)).Finite := by
    intro y
    have hint : ∀ᶠ v in Filter.cofinite, ev y v ∈ L v :=
      Filter.eventually_all.2 fun i => (y i).2
    refine (Filter.eventually_cofinite.1 (hae.and hint)).subset ?_
    intro w hw h'
    apply hw
    simp only
    rw [h'.1, Set.indicator_of_mem h'.2]
    rfl
  change IsLocallyConstant fun y => ∏ᶠ v, φ v (ev y v)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  by_cases hy : ∀ v ∉ S, ev y v ∈ L v
  ·
    let G : Set (κ → FiniteAdeleRing (𝓞 F) F) := {z | ∀ v ∉ S, ev z v ∈ L v}
    have hGe : G = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F => z i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ S → x.1 v ∈ v.adicCompletionIntegers F} := by
      ext z
      simp only [G, L, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, hev]
      exact ⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩
    have hGo : IsOpen G := by
      rw [hGe]
      exact isOpen_iInter_of_finite fun i =>
        (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)).preimage
          (continuous_apply i)
    have heq : ∀ z ∈ G, ∏ᶠ v, φ v (ev z v) = ∏ v ∈ hS.toFinset, φ v (ev z v) := by
      intro z hz
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      by_contra hvS
      apply hv
      have hφ : φ v = Set.indicator (L v) 1 := not_not.1 hvS
      simp only
      rw [hφ, Set.indicator_of_mem (hz v hvS)]
      rfl
    have hlc : IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => ∏ v ∈ hS.toFinset, φ v (ev z v) := by
      have : ∀ v, IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => φ v (ev z v) := fun v =>
        (hSB v).1.comp_continuous (hcont v)
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun z => ?_
      have h2 : ∀ᶠ w in nhds z, ∀ v ∈ hS.toFinset, φ v (ev w v) = φ v (ev z v) :=
        (Filter.eventually_all_finset _).2 fun v _ => (IsLocallyConstant.iff_eventually_eq _).1 (this v) z
      filter_upwards [h2] with w hw
      exact Finset.prod_congr rfl hw
    filter_upwards [hGo.mem_nhds hy, (IsLocallyConstant.iff_eventually_eq _).1 hlc y] with z hz hz'
    rw [heq z hz, heq y hy]
    exact hz'
  ·
    push_neg at hy
    obtain ⟨v, hvS, hvL⟩ := hy
    have hφ : φ v = Set.indicator (L v) 1 := not_not.1 hvS
    let U : Set (κ → FiniteAdeleRing (𝓞 F) F) := {z | ev z v ∉ L v}
    have hLc : IsClosed (L v) := by
      have e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        ext x; simp [L]
      rw [e]
      exact isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed
    have hUo : IsOpen U := hLc.isOpen_compl.preimage (hcont v)
    have h0 : ∀ z ∈ U, ∏ᶠ w, φ w (ev z w) = 0 := fun z hz =>
      finprod_eq_zero _ v (by show φ v (ev z v) = 0; rw [hφ, Set.indicator_of_notMem hz]) (hfin z)
    filter_upwards [hUo.mem_nhds hvL] with z hz
    rw [h0 z hz, h0 y hvL]

end GlobalTheory.AdelicCoordSB
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SBBox

theorem exists_nhds_zero_add_eq {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {Y : Type}
    [Zero Y] {g : X → Y} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ N ∈ nhds (0 : X), ∀ y, ∀ u ∈ N, g (y + u) = g y := by
  classical
  have hW : ∀ x : X, ∃ W ∈ nhds (0 : X), ∀ a ∈ W, ∀ b ∈ W, g (x + (a + b)) = g x := by
    intro x
    have h1 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ nhds (0 : X) := by
      refine (hg.isOpen_fiber (g x)).preimage (continuous_const.add continuous_id) |>.mem_nhds ?_
      simp
    obtain ⟨W, hW, hWW⟩ := exists_nhds_zero_half h1
    exact ⟨W, hW, fun a ha b hb => hWW a ha b hb⟩
  choose W hW0 hWg using hW
  let V : X → Set X := fun x => W x ∩ Neg.neg ⁻¹' W x
  have hV0 : ∀ x, V x ∈ nhds (0 : X) := fun x => Filter.inter_mem (hW0 x) (neg_mem_nhds_zero X (hW0 x))
  have hcov : tsupport g ⊆ ⋃ x : X, (fun y => y - x) ⁻¹' interior (V x) := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    simp only [Set.mem_preimage, sub_self]
    exact mem_interior_iff_mem_nhds.2 (hV0 x)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun x => (fun y => y - x) ⁻¹' interior (V x))
    (fun x => isOpen_interior.preimage (continuous_id.sub continuous_const)) hcov
  refine ⟨⋂ x ∈ t, V x, (Filter.biInter_finset_mem t).2 fun x _ => hV0 x, fun y u hu => ?_⟩
  have hu' : ∀ x ∈ t, u ∈ W x ∧ -u ∈ W x := fun x hx => by
    have := Set.mem_iInter₂.1 hu x hx
    exact ⟨this.1, this.2⟩
  have h0 : ∀ x, (0 : X) ∈ W x := fun x => mem_of_mem_nhds (hW0 x)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hyx' : y - x ∈ W x := (interior_subset hyx : y - x ∈ V x).1
    have e1 : g (y + u) = g x := by
      have := hWg x (y - x) hyx' u (hu' x hx).1
      rwa [show x + (y - x + u) = y + u by abel] at this
    have e2 : g y = g x := by
      have := hWg x (y - x) hyx' 0 (h0 x)
      rwa [show x + (y - x + 0) = y by abel] at this
    rw [e1, e2]
  · by_cases hyu : y + u ∈ tsupport g
    · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyu)
      have hyx' : y + u - x ∈ W x := (interior_subset hyx : y + u - x ∈ V x).1
      have e1 : g y = g x := by
        have := hWg x (y + u - x) hyx' (-u) (hu' x hx).2
        rwa [show x + (y + u - x + -u) = y by abel] at this
      have e2 : g (y + u) = g x := by
        have := hWg x (y + u - x) hyx' 0 (h0 x)
        rwa [show x + (y + u - x + 0) = y + u by abel] at this
      rw [e1, e2]
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

variable {F : Type} [Field F] [NumberField F]

def ballR (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (v.adicCompletion F) :=
  Valued.v.leAddSubgroup (v.intValuation r)

theorem mem_ballR {r : 𝓞 F} {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ ballR r v ↔ Valued.v x ≤ v.intValuation r := Iff.rfl

theorem isOpen_ballR {r : 𝓞 F} (hr : r ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (ballR r v : Set (v.adicCompletion F)) := by
  set c : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)
  have hcv : Valued.v c = v.intValuation r := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R v r
  have hc : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact (v.intValuation_ne_zero r hr) hcv.symm
  have e : (ballR r v : Set (v.adicCompletion F)) =
      (fun x => x / c) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x
    change Valued.v x ≤ v.intValuation r ↔ Valued.v (x / c) ≤ 1
    rw [map_div₀, ← hcv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
  rw [e]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_id.div_const c)

theorem ballR_subset (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (ballR r v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F := fun x hx => by
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (mem_ballR.1 hx).trans (v.intValuation_le_one r)

theorem eventually_ballR_eq {r : 𝓞 F} (hr : r ≠ 0) :
    ∀ᶠ v in Filter.cofinite, (ballR r v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F := by
  have h : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h).subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [← HeightOneSpectrum.intValuation_lt_one_iff_dvd]
  refine lt_of_le_of_ne (v.intValuation_le_one r) fun h1 => hv ?_
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_ballR, h1, HeightOneSpectrum.mem_adicCompletionIntegers]

end GlobalTheory.SBBox

namespace GlobalTheory.SBBox

theorem exists_box_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hr : ∀ i, ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ y : FiniteAdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y v) ≤ v.intValuation r) → y ∈ t i :=
    fun i => GlobalTheory.OpenSubAdele.exists_small_of_mem_nhds (ht i)
  choose r hr0 hrt using hr
  set R : 𝓞 F := ∏ i, r i
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hr0 i
  have hle : ∀ i (v : HeightOneSpectrum (𝓞 F)), v.intValuation R ≤ v.intValuation (r i) := by
    intro i v
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
    rw [show R = r i * c from hc, map_mul]
    exact mul_le_of_le_one_right' (v.intValuation_le_one c)
  refine ⟨ballR R, isOpen_ballR hR0, ballR_subset R, eventually_ballR_eq hR0, fun y u hu => ?_⟩
  refine hNg y u (hIt fun i _ => hrt i (u i) fun v => ?_)
  exact (mem_ballR.1 (hu i v)).trans (hle i v)

end GlobalTheory.SBBox
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.linearSection_finite_inOpen_off_badForm : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → ∀ (g : MvPolynomial (Fin T.N) F), (∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0) → (∀ (K : Type) [Field K] [Algebra F K] (y : Fin T.N → K), {x : T.Pt K | aeval (T.coords x.1) g ≠ 0 ∧ ∃ c : K, T.coords x.1 = c • y}.Finite) → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f ≠ 0 → (∀ x ∈ T.geomPts E (T.linSection E s), aeval (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1) g ≠ 0) → ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite ∧ T.InOpen E (T.linSection E s) := by
  first | exact @GlobalTheory.HSShort.Supp.finite_and_inOpen | exact GlobalTheory.HSShort.Supp.finite_and_inOpen | (intros; apply GlobalTheory.HSShort.Supp.finite_and_inOpen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdVertex



theorem exists_std_vertex : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    (∀ τ, V.sig τ = (V.rank, 0)) → IsSelfDualC V Λ → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∃ (fr : GL (Fin V.rank) D.host.E) (u : GfC V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V Λ hsig hpos hΛ S hS
  obtain ⟨fr0, hfr0⟩ := GlobalTheory.T.exists_orthonormalBasis_definite_hermitianSpace D V hsig hpos
  obtain ⟨x, hxx⟩ := GlobalTheory.T.exists_finiteAdelicUnitary_moves_selfDualLattice D V fr0 Λ hfr0 hΛ
  have hx : x ∈ GfC V := hxx.1
  have hxL := hxx.2
  obtain ⟨γ, h, k, hr⟩ := GlobalTheory.T.idempotent_support_hermitian_decomposition D V fr0 S hS x hx
  have hγ := hr.1
  have hh := hr.2.1
  have hsupp := hr.2.2.1
  have hkL := hr.2.2.2.2.1
  have hxe := hr.2.2.2.2.2
  obtain ⟨u, hur⟩ := GlobalTheory.T.rationalUnitary_conj_splitSupported_finiteAdelicPoint D V S γ h hγ hh hsupp
  have hu : u ∈ GfC V := hur.1
  have hue := hur.2.2
  refine ⟨γ * fr0, ⟨u, hu⟩, ?_, hur.2.1, ?_⟩
  · have e1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ * fr0).1 =
        Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 := by
      simp only [Formalism.UG.cT, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    rw [e1, Units.val_mul]
    calc _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 *
          (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1) * fr0.1 := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hγ, hfr0]
  · intro v
    have hγγ : γ.1.map (eToEAf D) * (γ⁻¹).1.map (eToEAf D) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hKK : (Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) ↔
        ((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) := fun w => by
      rw [hkL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w), Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]
    have key : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v)) =
        (Formalism.IndefR.Lev.finE V u).1 *ᵥ v := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxe, hue]
      congr 1
      calc _ = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 *
            ((Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1) * (γ⁻¹).1.map (eToEAf D) := by
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [hKK, Matrix.mul_one]
    have s1 := GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff D γ fr0 v
    have s2 := h1 ((γ⁻¹).1.map (eToEAf D) *ᵥ v)
    have s3 := hxL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v))
    rw [key] at s3
    exact s1.trans (s2.trans s3)

end GlobalTheory.FunObj.StdVertex
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionEll

theorem exists_GL_charpoly_eq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  intro E _ _ n P hP
  obtain ⟨hm, hn, -, hr⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : P.coeff 0 ≠ 0 := by
    intro h
    have hroot : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]
    have := hr τ 0 hroot
    simp at this
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) E, N.charpoly = P := by
    subst hn
    exact ⟨_, (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)⟩
  have hd : IsUnit N.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hN]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  exact ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hd).unit, hN⟩

end GlobalTheory.CompanionEll
end
