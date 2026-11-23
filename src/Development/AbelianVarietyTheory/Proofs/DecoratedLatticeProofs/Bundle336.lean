module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
public import Aesop.BuiltinRules
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle323
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocal
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal Pointwise

variable {D : D7}

theorem borel_Mx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  · intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

theorem lintegral_resS {S A B T : HSp D} (o : OrthDec S A B) (μ : Measure (WO S T)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (WO S T)) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (μA : Measure (WO A T)) (μB : Measure (WO B T))
    [μA.IsAddHaarMeasure] [μB.IsAddHaarMeasure] (FA : Set (WO A T)) (FB : Set (WO B T))
    (hA : IsAddFundamentalDomain (ratL T A) FA μA) (hB : IsAddFundamentalDomain (ratL T B) FB μB) :
    ∃ c : ℝ≥0, ∀ Φ : WO A T × WO B T → ℝ≥0∞, (∀ γ ∈ ratL T S, ∀ x, Φ (o.resS T (γ + x)) = Φ (o.resS T x)) →
      ∫⁻ x in 𝓕, Φ (o.resS T x) ∂μ = c • ∫⁻ y, Φ y ∂((μA.restrict FA).prod (μB.restrict FB)) := by
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  haveI : Countable (ratL T S) :=
    (TopologicalSpace.separableSpace_iff_countable.1 inferInstance : Countable (ratMx D T.rank S.rank))
  haveI : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun _ => (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  let e : WO S T ≃ₜ (WO A T × WO B T) :=
    { (o.resS T).toEquiv with continuous_toFun := o.continuous_resS T, continuous_invFun := o.continuous_resS_symm T }
  let em := e.toMeasurableEquiv
  haveI : (μ.map em).IsAddHaarMeasure :=
    (o.resS T).isAddHaarMeasure_map μ (o.continuous_resS T) (o.continuous_resS_symm T)
  obtain ⟨c, hmeq⟩ : ∃ c : ℝ≥0, μ.map em = c • μA.prod μB :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map em) (μA.prod μB)⟩
  refine ⟨c, fun Φ hper => ?_⟩
  have hqmp : QuasiMeasurePreserving em μ (μA.prod μB) :=
    ⟨em.measurable.aemeasurable, by rw [hmeq]; exact Measure.smul_absolutelyContinuous⟩
  have hprod := isAddFundamentalDomain_prod hA hB
  have hmem : ∀ g : (ratL T A).prod (ratL T B), (o.resS T).symm (g : WO A T × WO B T) ∈ ratL T S := fun g => by
    rw [o.mem_ratL_resS, AddEquiv.apply_symm_apply]; exact AddSubgroup.mem_prod.1 g.2
  have hP : IsAddFundamentalDomain (ratL T S) (em ⁻¹' (FA ×ˢ FB)) μ := by
    refine hprod.preimage_of_equiv hqmp (e := fun g => ⟨_, hmem g⟩) ⟨fun g g' h => ?_, fun h => ?_⟩ fun g x => ?_
    · exact Subtype.ext ((o.resS T).symm.injective (congrArg Subtype.val h))
    · refine ⟨⟨o.resS T h, AddSubgroup.mem_prod.2 ((o.mem_ratL_resS T h).1 h.2)⟩, Subtype.ext ?_⟩
      exact (o.resS T).symm_apply_apply h
    · change o.resS T ((o.resS T).symm (g : WO A T × WO B T) + x) = (g : WO A T × WO B T) + o.resS T x
      rw [map_add (f := _), AddEquiv.apply_symm_apply]
  rw [h𝓕.setLIntegral_eq hP (fun x => Φ (o.resS T x)) (fun g x => hper g g.2 x)]
  change ∫⁻ x in em ⁻¹' (FA ×ˢ FB), Φ (em x) ∂μ = _
  rw [← lintegral_map_equiv _ em, ← em.restrict_map, hmeq, Measure.restrict_smul, lintegral_smul_measure,
    Measure.prod_restrict]

end GlobalTheory.WeilSliceUnit

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal

variable {D : D7}

theorem enorm_sq_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ γ ∈ ratL T S, ∀ x, ‖f (γ + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
  rintro _ ⟨g, rfl⟩ x
  have h : ‖f (ratW T S g + x)‖ = ‖f x‖ := by rw [hf.quasi, norm_mul, hψ.1.2.1, one_mul]
  show ‖f (ratW T S g + x)‖ₑ ^ 2 = _
  rw [← ofReal_norm, ← ofReal_norm, h]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  intro D ψ S A B T o μ 𝓕 hμ h𝓕 f hf
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  obtain ⟨μA, FA, hA⟩ := exists_isCovolOne D T.rank A.rank
  obtain ⟨μB, FB, hB⟩ := exists_isCovolOne D T.rank B.rank
  haveI := hA.1
  haveI := hB.1
  have hFA : IsAddFundamentalDomain (ratL T A) FA μA := hA.2.1
  have hFB : IsAddFundamentalDomain (ratL T B) FB μB := hB.2.1
  obtain ⟨c, hc⟩ := lintegral_resS o μ 𝓕 h𝓕 μA μB FA FB hFA hFB
  have hslice := GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf
  have hΦ0 : Measurable fun y : WO A T × WO B T => ‖f ((o.resS T).symm y)‖ₑ ^ 2 :=
    ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hf.cont.comp (o.continuous_resS_symm T)))).measurable
  have e0 : ∀ hψ : IsStdChar D ψ (-1), ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ = c • ∫⁻ y, ‖f ((o.resS T).symm y)‖ₑ ^ 2
      ∂((μA.restrict FA).prod (μB.restrict FB)) := by
    intro hψ
    have h := hc (fun y => ‖f ((o.resS T).symm y)‖ₑ ^ 2) (fun γ hγ x => by
      simp only [AddEquiv.symm_apply_apply]; exact enorm_sq_periodic hψ hf γ hγ x)
    simpa only [AddEquiv.symm_apply_apply] using h
  refine ⟨fun χ χ' om hW p => ?_, fun χ χ' om hW p => ?_⟩
  · have hψ := hW.std
    have hF := hslice.1 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod_symm _ hΦ1.aemeasurable, lintegral_prod_symm _ hΦ0.aemeasurable]
    refine lintegral_congr fun v => ?_
    show ∫⁻ u in FA, ‖om p (fun u => f ((o.resS T).symm (u, v))) u‖ₑ ^ 2 ∂μA =
      ∫⁻ u in FA, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μA
    exact hW.om_unit μA FA hA.1 hFA p (fun u => f ((o.resS T).symm (u, v))) (hbox.1 v)
  · have hψ := hW.std
    have hF := hslice.2 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod _ hΦ1.aemeasurable, lintegral_prod _ hΦ0.aemeasurable]
    refine lintegral_congr fun u => ?_
    show ∫⁻ v in FB, ‖om p (fun v => f ((o.resS T).symm (u, v))) v‖ₑ ^ 2 ∂μB =
      ∫⁻ v in FB, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μB
    exact hW.om_unit μB FB hB.1 hFB p (fun v => f ((o.resS T).symm (u, v))) (hbox.2 u)

end GlobalTheory.WeilSliceUnit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SliceModelT

variable {D : D7}

theorem resT_symm_left {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) :
    (d.resT S).symm (u, 0) = GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank) u := by
  rw [OrthDec.resT_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem isThetaFunO_sliceT_left {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO S B) : IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v)) := {
  quasi γ u := by
    have e0 : (d.resT S).symm (ratW A S γ, 0) = ratW T S (d.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW A S γ + u, v) : WO S A × WO S B) = (ratW A S γ, (0 : WO S B)) + (u, v) := by simp
    show f ((d.resT S).symm (ratW A S γ + u, v)) = ψ (-(symplOH S A (ratW A S γ) u)) * f ((d.resT S).symm (u, v))
    rw [e, map_add (f := _), e0, hf.quasi, ← e0, d.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (hk _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resT S).symm (w, v))
    rw [← resT_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero, d.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const))
  smooth m L hL h0 w := by
    have e : ∀ t, (d.resT S).symm (w + L t, v) =
        (d.resT S).symm (w, v) + ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resT_symm_left, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth m ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _ }

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem ι_mul (a : AE D) (x : k) : p.ι (p.π a * x) = a * p.ι x := by
  have h1 : p.π a * x = p.π (a * p.ι x) := by rw [map_mul, p.π_ι]
  rw [h1, p.ι_π, mul_left_comm, ← p.ι_π, p.π_ι]

theorem mul_map_ι {m l n : Type} [Fintype l] (N : Matrix m l (AE D)) (M : Matrix l n k) :
    N * M.map p.ι = (N.map p.π * M).map p.ι := by
  ext i j

  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} (FS : Frame k S.rank n)

theorem beta_eq (hF : p.IsCoreFrame B s FA F₀) :
    F₀.β = fromCols (B.o.iA.map (prH p) * FA.β) (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) := by
  ext r (a | _)
  · exact hF.1 r a
  · exact hF.2 r

theorem col_eq : (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) =
    s • (B.o.iB.map (prH p) * Matrix.of fun j (_ : Unit) => prH p (B.ζ j)) := by
  ext r u

  simp [Matrix.mul_apply, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem qA_beta (hF : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [beta_eq p B hF, col_eq, Matrix.mul_fromCols, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, ← Matrix.map_mul, B.o.qA_iA, B.o.qA_iB, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, smul_zero]

theorem up_fromRows (hF : p.IsCoreFrame B s FA F₀) (x : Matrix n' n k) :
    p.up FS F₀ (fromRows x 0) = (B.o.resT S).symm (p.up FS FA x, 0) := by
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, mul_map_ι,
    beta_eq p B hF, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.map_map]
  simp only [Matrix.mul_assoc]
  rfl

theorem resT_up_fst (hF : p.IsCoreFrame B s FA F₀) (x : Matrix (n' ⊕ Unit) n k) :
    (B.o.resT S (p.up FS F₀ x)).1 = p.up FS FA x.toRows₁ := by
  rw [OrthDec.resT_apply]
  dsimp only
  rw [Place.up, Place.up, OrthDec.pA, rat, mul_map_ι, Matrix.map_map]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (B.o.qA.map (prH p) * F₀.β) * x * FS.γ = _
  rw [qA_beta p B hF]
  conv_lhs => rw [← fromRows_toRows x]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

def rowsH (n n' : Type) [Fintype n] [Fintype n'] : Matrix (n' ⊕ Unit) n k ≃ₜ Matrix n' n k × (n → k) where
  toFun x := (x.toRows₁, x (Sum.inr ()))
  invFun q := fromRows q.1 (Matrix.of fun _ => q.2)
  left_inv x := by
    ext (i | i) j <;> rfl
  right_inv q := by
    ext i j <;> rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_apply _)
    exact continuous_pi fun i => continuous_apply (Sum.inl i)
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    rcases i with i | i
    · exact (continuous_apply i).comp continuous_fst
    · exact continuous_snd

def tens (a : SB (n → k)) : SB (Matrix n' n k) →ₗ[ℂ] SB (Matrix (n' ⊕ Unit) n k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (rowsH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ a)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : SB (n → k)) (Ξ : SB (Matrix n' n k)) (x : Matrix (n' ⊕ Unit) n k) :
    (tens a Ξ).1 x = Ξ.1 x.toRows₁ * a.1 (x (Sum.inr ())) := rfl

end GlobalTheory.SliceModelT


open GlobalTheory.SliceModelT in
theorem GlobalTheory.SliceModelT.main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS hF T₀ hT a ha v
  let a' : SB (n → k) := ⟨a, ha⟩
  let T₁ : SB (Matrix n' n k) →ₗ[ℂ] (WO S B.A → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO S B.A => (B.o.resT S).symm (u, v))) ∘ₗ T₀ ∘ₗ tens a'
  have hT₁ : ∀ Ξ u, T₁ Ξ u = T₀ (tens a' Ξ) ((B.o.resT S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact isThetaFunO_sliceT_left B.o (hT.theta _) v
  · have h1 := hT.trans (fromRows x 0) (tens a' Φ) (tens a' Φ') (fun t => by
      have e1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
        ext i j; simp [Matrix.toRows₁, Matrix.fromRows_apply_inl]
      have e2 : (t + fromRows x (0 : Matrix Unit n k) : Matrix (n' ⊕ Unit) n k) (Sum.inr ()) = t (Sum.inr ()) := by
        funext j; simp [Matrix.fromRows_apply_inr]
      rw [tens_apply, tens_apply, hΦ, e1, e2])
    funext u
    rw [hT₁, h1, up_fromRows p B S FS hF]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · set Y : WO S B.V₀ := (B.o.resT S).symm (y, 0) with hYdef
    have hY : IsHalf (cA D p.e) Y := by
      intro i j
      rw [hYdef, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hy l j]
    have h1 := hT.modul Y hY (tens a' Φ) (tens a' Φ') (fun t => by
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resT, resT_up_fst p B S FS hF, hYdef, AddEquiv.apply_symm_apply,
        symplO_zero_right', add_zero, mul_assoc])
    funext u
    rw [hT₁, h1]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a' Ξ := Subtype.ext (funext hΨ)
    rw [e, hT₁]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ f₀ Φ f : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → ∀ g : GA D S, (∀ x, Φ x ≠ 0 → Φ (actO S T g 1 x) = 0) → ∃ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0 ∧ (actO S T g⁻¹ 1 (-(y i))).map (infPart D) = 0) ∧ ∑ i, a i • heisO ψ S T (y i) f = f ∧ ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) f = 0 := by
  first | exact @GlobalTheory.HalfSep.sep | exact GlobalTheory.HalfSep.sep | (intros; apply GlobalTheory.HalfSep.sep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idempotentHalf_mem_completedHomLattice_iff_local : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) := by
  first | exact @GlobalTheory.AdForm.HalfLat.half_mem_latO_iff | exact GlobalTheory.AdForm.HalfLat.half_mem_latO_iff | (intros; apply GlobalTheory.AdForm.HalfLat.half_mem_latO_iff <;> assumption)
end
