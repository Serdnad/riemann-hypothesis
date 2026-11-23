module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle005
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle003
public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle028
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle003
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HocolimAugmentationInjectiveOfPurityInputs
public import Development.EtaleCohomology.CohomologicalPurity.Bundle040
public import Development.EtaleCohomology.CohomologicalPurity.Bundle018
public import Development.EtaleCohomology.CohomologicalPurity.FinLeafCl
import Development.EtaleCohomology.CohomologicalPurity.Bundle037
public import Development.EtaleCohomology.CohomologicalPurity.Bundle007
import Development.EtaleCohomology.CohomologicalPurity.FinLeafThom
public import Development.EtaleCohomology.CohomologicalPurity.Bundle005
public import Development.EtaleCohomology.CohomologicalPurity.Bundle025
public import Development.EtaleCohomology.CohomologicalPurity.Bundle016
public import Development.EtaleCohomology.CohomologicalPurity.Bundle036
public import Development.EtaleCohomology.CohomologicalPurity.Bundle026
public import Development.EtaleCohomology.CohomologicalPurity.Bundle024
public import Development.EtaleCohomology.CohomologicalPurity.Bundle038
public import Development.EtaleCohomology.CohomologicalPurity.Bundle030
public import Development.EtaleCohomology.CohomologicalPurity.Bundle031
public import Development.EtaleCohomology.CohomologicalPurity.Bundle023
public import Development.EtaleCohomology.CohomologicalPurity.Bundle028
public import Development.EtaleCohomology.CohomologicalPurity.Bundle033
public import Development.EtaleCohomology.CohomologicalPurity.Bundle027
public import Development.EtaleCohomology.CohomologicalPurity.Bundle029
public import Development.EtaleCohomology.CohomologicalPurity.LeafPrdRingPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle017
public import Development.EtaleCohomology.CohomologicalPurity.Bundle032
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
public import Development.EtaleCohomology.CohomologicalPurity.LeafFstHocPf

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

private theorem bij_transport {ι X X' : Type*} {Y Y' : ι → Type*} (c : X ≃ X') (d : ∀ i, Y i ≃ Y' i)
    (g : ∀ i, X → Y i) (f : ∀ i, X' → Y' i) (h : ∀ i x, f i (c x) = d i (g i x))
    (hb : Function.Bijective fun x i => g i x) : Function.Bijective fun x i => f i x := by
  obtain ⟨hi, hs⟩ := hb
  refine ⟨fun x y hxy => ?_, fun b => ?_⟩
  · obtain ⟨x, rfl⟩ := c.surjective x
    obtain ⟨y, rfl⟩ := c.surjective y
    refine congrArg c (hi (funext fun i => (d i).injective ?_))
    have := congrFun hxy i
    simpa only [h] using this
  · obtain ⟨x, hx⟩ := hs fun i => (d i).symm (b i)
    refine ⟨c x, funext fun i => ?_⟩
    have := congrFun hx i
    simp only at this
    simp only [h, this, Equiv.apply_symm_apply]

private theorem sum_transport {W Y I : Type*} [AddCommGroup W] [AddCommGroup Y] [Fintype I] (a : I → ℤ) (e : Y ≃+ W)
    (f : I → Y) (g : I → W) (h : ∀ i, e (f i) = g i) (key : ∑ i, a i • g i = 0) : ∑ i, a i • f i = 0 := by
  apply e.injective

  rw [map_zero, map_sum]
  simp only [map_zsmul, h]
  exact key

variable {l : ℕ} [Fact l.Prime]

private theorem empty_isDec {A : Test l} (h : Subsingleton A.obj.A) :
    IsDec (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam A) := by
  refine ⟨fun x y _ => Subsingleton.elim x y, fun b => ⟨0, ?_⟩⟩
  funext e
  exact e.elim

private theorem locZero_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    {Q P : PAlg l ⥤ Type} {I : Type} [Fintype I] {a : I → ℤ} {u : I → (Q ⟶ P)} (hz : TZero a u) :
    Pa.LocZero (Q := testι l ⋙ Q) (P := testι l ⋙ P) a (fun i => Functor.whiskerLeft (testι l) (u i)) := by
  intro A y
  obtain ⟨S, hS, hs⟩ := hz A y
  refine ⟨S, (hPa A S).2 hS, fun s => ?_⟩
  rcases hs s with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((hPa _ _).2 (empty_isDec h0))

private theorem add_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    (n : ℕ) (hacr : AcrAdd) (F' : Coef (Test l)) (c : ∀ A, (testι l ⋙ AcrF l n).obj A ≃+ F'.obj A)
    (hc : ∀ {A B : Test l} (φ : A ⟶ B) (x : (testι l ⋙ AcrF l n).obj A),
      c B (((testι l ⋙ AcrF l n).map φ).hom x) = (F'.map φ).hom (c A x)) : Pa.Add F' := by
  intro A S hS
  exact bij_transport (c A).toEquiv (fun i => (c (S.B i)).toEquiv) (fun i x => PAlg.mapAcr (S.f i).hom n x)
    (fun i x => (F'.map (S.f i)).hom x) (fun i x => (hc (S.f i) x).symm) (hacr l n A S ((hPa A S).1 hS))

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.sumMH :
    UpperTheory.Ru.crystallineComparison.SumMH := by
  intro l _ Q P I _ a u hz n j x
  refine (partsEx l).elim fun Pa hPa => (theoryEx (Test l)).elim fun T hT => ?_
  refine (hT (Acris l) (testι l ⋙ AcrF l n)).elim fun F' h1 => h1.elim fun c h2 => h2.elim fun e h3 => ?_
  have hAdd : Pa.Add F' := add_of hPa n acrAdd F' c h3.1
  have key := locSum (Test l) Pa T F' hAdd (testι l ⋙ Q) (testι l ⋙ P) I a
    (fun i => Functor.whiskerLeft (testι l) (u i)) (locZero_of hPa hz) j
  have hp : ∀ i, e (testι l ⋙ Q) j (pullH (u i) n j x) =
      T.pull (Functor.whiskerLeft (testι l) (u i)) F' j (e (testι l ⋙ P) j x) := fun i =>
    h3.2 (Functor.whiskerLeft (testι l) (u i)) (pullMor (u i) n) rfl (fun _ _ => HEq.rfl) j x
  exact sum_transport a (e (testι l ⋙ Q) j) _ _ hp (key (e (testι l ⋙ P) j x))
end
end

section

theorem UpperTheory.Et.purAll : LateralTheory.CohomologicalPurity.LeafTube ∧ LateralTheory.CohomologicalPurity.LeafGysin ∧ LateralTheory.CohomologicalPurity.Goal := by
  have h_EPur_LeafAW : LateralTheory.CohomologicalPurity.LeafAW := LateralTheory.Fin.LeafAW.intersectionNumber_baseChange
  have h_EPur_LeafBd : LateralTheory.CohomologicalPurity.LeafBd := by apply LateralTheory.Fin.LeafBd.intersectionNumber_baseChange
  have h_EPur_LeafCl : LateralTheory.CohomologicalPurity.LeafCl := by apply LateralTheory.Fin.LeafCl.intersectionNumber_baseChange
  have h_EPur_LeafChart : LateralTheory.CohomologicalPurity.LeafChart := by apply LateralTheory.Fin.LeafChart.intersectionNumber_baseChange
  have h_EPur_LeafHens : LateralTheory.CohomologicalPurity.LeafHens := by apply LateralTheory.Fin.LeafHens.intersectionNumber_baseChange
  have h_EPur_LeafIndExc : LateralTheory.CohomologicalPurity.LeafIndExc := by apply LateralTheory.Fin.LeafIndExc.intersectionNumber_baseChange
  have h_EPur_LeafThom : LateralTheory.CohomologicalPurity.LeafThom := by apply LateralTheory.Fin.LeafThom.intersectionNumber_baseChange
  have h_EPur_LeafSemi : LateralTheory.CohomologicalPurity.LeafSemi := by apply LateralTheory.Fin.LeafSemi.intersectionNumber_baseChange
  have h_EPur_LeafExc : LateralTheory.CohomologicalPurity.LeafExc := by apply LateralTheory.Fin.LeafExc.intersectionNumber_baseChange
  have h_EPur_LeafPurNat : LateralTheory.CohomologicalPurity.EtalePurityNaturality := by apply LateralTheory.CohomologicalPurity.LeafPurNat_of
  have h_EPur_LeafPurProj : LateralTheory.CohomologicalPurity.EtalePurityProjection := by apply LateralTheory.CohomologicalPurity.LeafPurProj_of
  have h_EPur_LeafPurRed : LateralTheory.CohomologicalPurity.EtalePurityReduction := by apply LateralTheory.CohomologicalPurity.LeafPurRed_of
  have h_EPur_TubeCut_LeafChPush : LateralTheory.CohomologicalPurity.TubeCut.LeafChPush := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafChPush_of
  have h_EPur_TubeCut_LeafHKSplit : LateralTheory.CohomologicalPurity.TubeCut.LeafHKSplit := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHKSplit_of
  have h_relative : LateralTheory.CohomologicalPurity.TubeCut.LeafRel := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRel_of <;> assumption
  have h_equivalence_of_excision : LateralTheory.CohomologicalPurity.TubeCut.LeafEqvOfExc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafEqvOfExc_of <;> assumption
  have h_EPur_TubeCut_LeafChiSq : LateralTheory.CohomologicalPurity.TubeCut.LeafChiSq := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafChiSq_of
  have h_excision_of_equivalence : LateralTheory.CohomologicalPurity.TubeCut.LeafExcOfEqv := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafExcOfEqv_of_sq <;> assumption
  have h_EPur_TubeCut_LeafMLev : LateralTheory.CohomologicalPurity.TubeCut.LeafMLev := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafMLev_of
  have h_excision_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel_of <;> assumption
  have h_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafLevel := by apply LateralTheory.CohomologicalPurity.LeafLevelPf.LeafLevel_of
  have h_pullback_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafPbSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPbSum_of
  have h_double_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafDblSum := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDblSum_of <;> assumption
  have h_EPur_TubeCut_LeafDiscSumH : LateralTheory.CohomologicalPurity.TubeCut.LeafDiscSumH := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDiscSumH
  have h_chains_sum : LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafChainsSum := by apply LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafChainsSum_of
  have h_EPur_TubeCut_SumCut_LeafHKSum : LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafHKSum := by apply LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafHKSum_of
  have h_sum₂ : LateralTheory.CohomologicalPurity.TubeCut.LeafSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafSum_of <;> assumption
  have h_EPur_TubeCut_LeafHsSum : LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum_of_dbl <;> assumption
  have h_excision_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafExcHoc := by apply UpperTheory.Cb.etale_excision_hocolim_of_local_properties <;> assumption
  have h_EPur_TubeCut_LeafDiscPb : LateralTheory.CohomologicalPurity.TubeCut.LeafDiscPb := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDiscPb
  have h_universal_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafUnivSum := by apply LateralTheory.CohomologicalPurity.TubeCut.leafUnivSum
  have h_EPur_TubeCut_LeafFstHoc : LateralTheory.CohomologicalPurity.TubeCut.LeafFstHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafFstHoc_of <;> assumption
  have h_augmentation_injective_at : LateralTheory.CohomologicalPurity.TubeCut.EtaleAugInjAt := by apply UpperTheory.Cb.hocolimAugmentation_injective_of_purity_inputs <;> assumption
  have h_augmentation_injective : LateralTheory.CohomologicalPurity.TubeCut.LeafAugInj := by apply LateralTheory.CohomologicalPurity.TubeCut.EtaleAugInj_of_augInjAt <;> assumption
  have h_augmentation_surjective : LateralTheory.CohomologicalPurity.TubeCut.LeafAugSurj := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAugSurj_of
  have h_EPur_TubeCut_LeafHomLoc : LateralTheory.CohomologicalPurity.TubeCut.LeafHomLoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHomLoc_of
  have h_augmentation_local : LateralTheory.CohomologicalPurity.TubeCut.LeafAugLocal := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAugLocal_of <;> assumption
  have h_EPur_TubeCut_LeafLocBase : LateralTheory.CohomologicalPurity.TubeCut.EtaleLocBase := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocBase_of
  have h_quasi_isomorphism_local : LateralTheory.CohomologicalPurity.TubeCut.LeafQisLocal := by apply LateralTheory.CohomologicalPurity.QisLocalPf.LeafQisLocal_of
  have h_EPur_TubeCut_LeafLoc : LateralTheory.CohomologicalPurity.TubeCut.LeafLoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocCutAll.goal_of <;> assumption
  have h_EPur_TubeCut_LeafLocExc : LateralTheory.CohomologicalPurity.TubeCut.LeafLocExc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocExc_of <;> assumption
  have h_EPur_TubeCut_LeafZ : LateralTheory.CohomologicalPurity.TubeCut.LeafZ := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafZ_of
  have h_EPur_TubeCut_LeafLocFst : LateralTheory.CohomologicalPurity.TubeCut.LeafLocFst := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocFst_of <;> assumption
  have h_EPur_TubeCut_LeafAbv : LateralTheory.CohomologicalPurity.TubeCut.LeafAbv := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAbv_of
  have h_EPur_TubeCut_LeafLocHen : LateralTheory.CohomologicalPurity.TubeCut.LeafLocHen := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocHen_of <;> assumption
  have h_quotient : LateralTheory.CohomologicalPurity.TubeCut.LeafQuot := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafQuot_of
  have h_EPur_TubeCut_LeafLocIso : LateralTheory.CohomologicalPurity.TubeCut.LeafLocIso := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocIso_of <;> assumption
  have h_EPur_TubeCut_LeafActNat : LateralTheory.CohomologicalPurity.TubeCut.LeafActNat := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafActNat_of
  have h_excision_affine : LateralTheory.CohomologicalPurity.TubeCut.LeafExcAff := by apply LateralTheory.CohomologicalPurity.TubeCut.leafExcAff_pf
  have h_EPur_TubeCut_LeafHensH : LateralTheory.CohomologicalPurity.TubeCut.LeafHensH := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHensH_of
  have h_product_affine : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdAff := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdAff_of' <;> assumption
  have h_product_ring : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdRing := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdRing_of <;> assumption
  have h_EPur_TubeCut_LeafLocPrd : LateralTheory.CohomologicalPurity.TubeCut.LeafLocPrd := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocPrd_of <;> assumption
  have h_product_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdLevel := by apply UpperTheory.productLevelwise_of_alexanderWhitney <;> assumption
  have h_product_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdHoc_of <;> assumption
  have h_EPur_TubeCut_LeafPush : LateralTheory.CohomologicalPurity.TubeCut.LeafPush := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPush_of
  have h_refinement : LateralTheory.CohomologicalPurity.TubeCut.LeafRefine := by apply LateralTheory.CohomologicalPurity.TubeCut.EtaleRefine_of_push <;> assumption
  have h_relative_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafRelLev := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRelLev_of
  have h_relative_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafRelHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRelHoc_of <;> assumption
  have h_EPur_LeafTube : LateralTheory.CohomologicalPurity.LeafTube := by apply LateralTheory.CohomologicalPurity.TubeCut.goal_of <;> assumption
  have h_EPur_LeafPur : LateralTheory.CohomologicalPurity.LeafPur := by apply LateralTheory.CohomologicalPurity.EtalePurity_of_parts <;> assumption
  have h_EPur_LeafGysin : LateralTheory.CohomologicalPurity.LeafGysin := by apply LateralTheory.CohomologicalPurity.LeafGysin_of <;> assumption
  have h_cohomological_purity : LateralTheory.CohomologicalPurity.Goal := by apply LateralTheory.CohomologicalPurity.goal_of <;> assumption
  exact ⟨h_EPur_LeafTube, h_EPur_LeafGysin, h_cohomological_purity⟩

theorem UpperTheory.Et.purGysin : LateralTheory.CohomologicalPurity.LeafGysin := UpperTheory.Et.purAll.2.1
end
