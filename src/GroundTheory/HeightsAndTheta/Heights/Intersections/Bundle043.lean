module

import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
  ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionIntegral

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem ae_eval_ne_zero {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf => by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy => ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq => ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

theorem ptsIntegral_logNormRat (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    {L : Fin n → HermLine ι} {A B : HermLine ι} {f g : MRing ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hf : IsSectionOn P (A.tensor B) f) (hg : IsSectionOn P B g) :
    ptsIntegral P (pot L) (logNormRat A f g) =
      ptsIntegral P (pot L) (logNorm (A.tensor B) f) - ptsIntegral P (pot L) (logNorm B g) := by
  have hAB := isSmoothHerm_tensor hA hB
  obtain ⟨α, -, hfα, hfP⟩ := id hf
  obtain ⟨β, -, hgβ, hgP⟩ := id hg
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB hf) (hInt K ι P n _ L _ g hP hΨg hL hB hg)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hfα⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hgβ⟩ hgP]
      with y hyf hyg
    rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hs := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hs.2.1
      have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
      have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← sub_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / B.h z)
      rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
        Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
        Real.log_div hf0.ne' hg0.ne']
      ring
    · simp
  · simp

theorem isSmoothHerm_pull {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem pullDeg_add (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by
  funext k'
  simp only [pullDeg, Pi.add_apply]
  unfold Function.extend
  split_ifs <;> simp


omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem isPullHerm_tensor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : HermLine ι}
    {A' B' : HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by
  refine ⟨?_, fun z' => ?_⟩
  · show A'.a + B'.a = pullDeg κ (A.a + B.a)
    rw [pullDeg_add, hA.1, hB.1]
  · show A'.h z' * B'.h z' = A.h _ * B.h _
    rw [hA.2, hB.2]


open Classical in
theorem sum_block (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {s : MRing ι} {α : K → ℕ} (hs : IsMultiHomog s α) :
    IsMultiHomog (rename v s) (Function.extend κ α 0) := by
  apply GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.isMultiHomog_rename <;> assumption

end ArithmeticIntersectionIntegral


open ArithmeticIntersectionIntegral in
theorem ArithmeticIntersectionIntegral.proof (hInt : PtsIntegrableStatement) (hSec : IntersectionWithSection.Statement) : ArithmeticIntersectionIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' f g hv hP' hP hJ hL hLL' hA hAA' hfg
  obtain ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ := hfg
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hBB' := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv (HermLine.sqMetric (ι := ι) β)
  have hB' := isSmoothHerm_pull hv hB hBB'
  have hA' := isSmoothHerm_pull hv hA hAA'
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have hfs : IsSectionOn (imageZ v P') (A.tensor (HermLine.sqMetric β)) f := by
    refine ⟨α, fun k => ?_, hf, hfP⟩
    show A.a k + (β k : ℤ) = α k
    rw [← hαβ k]
    ring
  have hgs : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩
  have hfs' : IsSectionOn P' (A'.tensor (IndefiniteRowSideFullHecke.Inter.pullHerm hv (HermLine.sqMetric β))) (rename v f) := by
    refine ⟨Function.extend κ α 0, fun k' => ?_, isMultiHomog_rename hv hf,
      fun h => hfP (Ideal.mem_comap.mpr h)⟩
    show A'.a k' + pullDeg κ (fun k => (β k : ℤ)) k' = _
    rw [hAA'.1, pullDeg, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply, ← hαβ k]
      ring
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hgs' : IsSectionOn P' (IndefiniteRowSideFullHecke.Inter.pullHerm hv (HermLine.sqMetric (ι := ι) β)) (rename v g) := by
    refine ⟨Function.extend κ β 0, fun k' => ?_, isMultiHomog_rename hv hg,
      fun h => hgP (Ideal.mem_comap.mpr h)⟩
    show pullDeg κ (fun k => (β k : ℤ)) k' = _
    rw [pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  rw [ptsIntegral_logNormRat hInt hP' hL' hA' hB' hfs' hgs', ptsIntegral_logNormRat hInt hP hL hA hB hfs hgs,
    hSec K ι K' ι' κ v P' n G J L L' _ _ f hv hP' hP hJ hL hLL' (isSmoothHerm_tensor hA hB)
      (isPullHerm_tensor hAA' hBB') hfs,
    hSec K ι K' ι' κ v P' n G J L L' _ _ g hv hP' hP hJ hL hLL' hB hBB' hgs, mul_sub]

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem IntClosureLocFinite.proof (h : RelAlgClosureFinite.Statement) :
    IntClosureLocFinite.Statement := by
  classical
  intro F L _ _ φ S hS A T hDA hloc
  let : Algebra A L := (φ.comp A.subtype).toAlgebra

  let D : Subring F := Subring.closure (T : Set F)
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.equiv ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T))
      (Subring.closureEquivAdjoinInt _).symm
  let : Algebra D L := (φ.comp D.subtype).toAlgebra
  let : Algebra D A := (Subring.inclusion hDA).toAlgebra
  have : IsScalarTower D A L := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let K := FractionRing D
  have hinj : Function.Injective (φ.comp D.subtype) := φ.injective.comp Subtype.val_injective
  let : Algebra K L := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower D K L :=
    IsScalarTower.of_algebraMap_eq fun d => (IsFractionRing.lift_algebraMap hinj d).symm
  have hKS : IntermediateField.adjoin K (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subfield.closure (S : Set L) := hS ▸ Subfield.mem_top x
    exact (Subfield.closure_le (t := (IntermediateField.adjoin K (S : Set L)).toSubfield)).mpr
      (IntermediateField.subset_adjoin K _) hx

  let M := algebraicClosure K L
  have : FiniteDimensional K M := h K L S hKS
  have : IsScalarTower D M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : Module.Finite D (integralClosure D M) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full D K M
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.image fun g : integralClosure D M => ((g : M) : L), fun x hx => ?_⟩

  let U : Submonoid D := (IsUnit.submonoid A).comap (Subring.inclusion hDA)
  have : IsLocalization U A := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {d₁ d₂} hd => ⟨1, ?_⟩⟩
    · obtain ⟨b, hb, c, hc, hc0, hcA, hzc⟩ := hloc z z.2
      have hunit : IsUnit (Subring.inclusion hDA ⟨c, hc⟩) :=
        IsUnit.of_mul_eq_one (⟨c⁻¹, hcA⟩ : A) (Subtype.ext (mul_inv_cancel₀ hc0))
      exact ⟨(⟨b, hb⟩, ⟨⟨c, hc⟩, hunit⟩), Subtype.ext hzc⟩
    · rw [Subring.inclusion_injective hDA hd]
  obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := A) U x hx

  obtain ⟨y, hy⟩ : ∃ y : L, y = (⟨m, hm⟩ : U) • x := ⟨_, rfl⟩
  rw [← hy] at hmx
  have hyK : IsIntegral K y := hmx.tower_top
  let yM : M := ⟨y, hyK⟩
  have hyMint : IsIntegral D yM := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom D M L) (fun a b hab => Subtype.ext hab)]
    exact hmx
  have hyspan : (⟨yM, hyMint⟩ : integralClosure D M) ∈ Submodule.span D (s : Set _) :=
    hs ▸ Submodule.mem_top
  let f : integralClosure D M →ₗ[D] L :=
    (IsScalarTower.toAlgHom D M L).toLinearMap ∘ₗ (integralClosure D M).val.toLinearMap
  have hyD : y ∈ Submodule.span D ((s.image fun g : integralClosure D M => ((g : M) : L)) : Set L) := by
    have hmap := Submodule.mem_map_of_mem (f := f) hyspan
    rw [Submodule.map_span] at hmap
    rw [Finset.coe_image]
    exact hmap
  have hyA := Submodule.span_subset_span D A _ hyD

  have hu : IsUnit (algebraMap D A m) := hm
  have hyu : y = (hu.unit : A) • x := by
    rw [hy, Submonoid.smul_def, IsUnit.unit_spec, algebraMap_smul]
  have hx' : x = ((hu.unit⁻¹ : Aˣ) : A) • y := by
    rw [hyu, smul_smul, Units.inv_mul, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ hyA

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalFinite.proof (hD : regularityLocalDimension_holds.Statement) : RegularityLocalFinite.Statement := by
  intro K _ ι _ P s a W y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  have hfinRes : Finite (IsLocalRing.ResidueField (locRing P W)) :=
    (regularityLocalResidue_holds.proof K ι P s a W (fun i => i.elim0) hP hs hsP hW).1
  letI := hfinRes
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  have hcard := card_eq_card_residueField_pow_length (locRing P W ⧸ locIdeal P W y) hfin
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField (locRing P W)) := Nat.card_pos
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hpos.ne'

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsMonoSemiPos.proof (hInt : PtsIntegrableStatement) (hHess : SheetHessPSD.Statement) :
    PtsMonoSemiPos.Statement := by
  intro K _ ι _ Q e M E D t hQ hMs hMp hE ht hD hDa hle
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · rw [dite_eq_right hΨ, dite_eq_right hΨ]
  rw [dite_eq_left hΨ, dite_eq_left hΨ]
  set Ψ := hΨ.choose with hΨdef
  have hΨg : IsGoodProj Q Ψ := hΨ.choose_spec
  unfold ptsIntegralAt
  have hD1 : IsSectionOn Q D 1 := by
    refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
      fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have key : ∀ y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm D 1) y w := by
    intro y w
    unfold sheetDensity
    split_ifs <;> simp [logNorm, Real.log_inv]
  have h1 := hInt K ι Q e Ψ M E t hQ hΨg hMs hE ht
  have h2 : Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w) := by
    simp only [key, finsum_neg_distrib]
    exact (hInt K ι Q e Ψ M D 1 hQ hΨg hMs hD hD1).neg
  obtain ⟨a, -, hta, htQ⟩ := ht
  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJQ : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ hQ hΨg hJ hJQ
  refine integral_mono_ae h1 h2 ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι Q e Ψ hQ hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · rw [dite_eq_left hγ, dite_eq_left hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have ht0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) ≠ 0 := by
      intro h0
      refine hyB ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [map_mul, map_mul, h0, mul_zero]
    have hma : 0 ≤ maDensity (fun j y' => pot M j (hγ.choose y')) y :=
      ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j =>
        hHess K ι Q e Ψ (M j) y w hγ.choose (hMs j) (hMp j) hγ.choose_spec
    exact mul_le_mul_of_nonneg_right (hle _ hmem ht0) hma
  · rw [dite_eq_right hγ, dite_eq_right hγ]

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem GenericPointsCount.proof (hGood : GenericPointsAvoidBadLocus.Statement) : GenericPointsCount.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n G i Ψ hv hP' hP hΨ hi
  obtain ⟨D, a, hDa, hDP, hcount⟩ := hGood K ι K' ι' κ v P' n G i hv hP' hP hi
  have hJ : IsMultiHomogIdeal (Ideal.span {D}) :=
    ⟨{D}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hDa⟩, rfl⟩
  have hJP : ¬ Ideal.span {D} ≤ imageZ v P' := fun hle => hDP (hle (Ideal.subset_span rfl))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (projB_null Ψ hP hΨ hJ hJP)] with y hy
  rintro w ⟨z, hz, rfl, hΨz⟩
  have hD : eval z (map (Int.castRingHom ℂ) D) ≠ 0 := by
    intro h0
    refine hy ⟨z, hz, ⟨hz.1, fun f hf => ?_⟩, hΨz⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, h0, mul_zero]
  have hΨ0 : Ψ (segre z) 0 = 1 := by
    have := congrFun hΨz 0
    simpa using this
  rw [← hcount z hz hD]
  congr 1
  ext O
  constructor
  · rintro ⟨z', hz', rfl, hw⟩
    refine ⟨z', hz', rfl, ?_⟩
    have hμ : Ψ (segre fun p => z' (v p)) 0 ≠ 0 := by
      intro h0
      rw [h0, inv_zero, zero_smul] at hw
      rw [← hw, map_zero] at hΨ0
      exact zero_ne_one hΨ0
    refine sameOrbit_of_segre hz.1 (Ψ (segre fun p => z' (v p)) 0) hμ ?_
    rw [← hw, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  · rintro ⟨z', hz', rfl, hs⟩
    refine ⟨z', hz', rfl, ?_⟩
    obtain ⟨c, hc, hcz⟩ := hs
    have hμ : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
    rw [hcz, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, hΨ0, mul_one, smul_smul, inv_mul_cancel₀ hμ,
      one_smul]

end GroundTheory.Heights₂.Heights.Inter
end
end
