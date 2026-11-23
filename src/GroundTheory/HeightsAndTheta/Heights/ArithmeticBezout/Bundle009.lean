module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle001
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace SectionComponents

variable {F : Type} [Field F] {n : ℕ}

theorem exists_ringKrullDim_quotient_eq (Q : Ideal (MvPolynomial (Fin n) F)) [Q.IsPrime] :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = m := by
  have _ : Algebra.FiniteType F (MvPolynomial (Fin n) F ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) (Ideal.Quotient.mkₐ_surjective F Q)
  have hlt := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_lt_top (k := F)
    (A := MvPolynomial (Fin n) F ⧸ Q)
  have hnn := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ Q)
  cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) with
  | bot => rw [h] at hnn; exact absurd hnn (by simp)
  | coe y =>
    rw [h] at hlt
    have : y ≠ ⊤ := fun hy => by subst hy; exact lt_irrefl _ hlt
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp this
    exact ⟨m, rfl⟩

theorem ringKrullDim_quotient_add_one_le_of_lt {W' W : Ideal (MvPolynomial (Fin n) F)}
    [W'.IsPrime] (hlt : W' < W) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W') := by
  set p : Ideal (MvPolynomial (Fin n) F ⧸ W') := W.map (Ideal.Quotient.mk W')
  have hp : p ≠ ⊥ := by
    obtain ⟨x, hxW, hxW'⟩ := SetLike.exists_of_lt hlt
    intro h
    apply hxW'
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk W' x ∈ p := Ideal.mem_map_of_mem _ hxW
    rwa [h, Ideal.mem_bot] at this
  have hquot : ringKrullDim ((MvPolynomial (Fin n) F ⧸ W') ⧸ p) =
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hlt.le)
  have := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le p hp
  rwa [hquot] at this

theorem ringKrullDim_quotient_add_one_eq {P W : Ideal (MvPolynomial (Fin n) F)} [P.IsPrime]
    {f : MvPolynomial (Fin n) F} (hf : f ∉ P) (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) F ⧸ P) := by
  have hWprime : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  set B := MvPolynomial (Fin n) F ⧸ P
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) (Ideal.Quotient.mkₐ_surjective F P)
  set W' : Ideal B := W.map (Ideal.Quotient.mk P)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hf
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk P f ∈ W' := Ideal.mem_map_of_mem _ hfW
    rwa [h, Ideal.mem_bot] at this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq W
  obtain ⟨k, hk⟩ := exists_ringKrullDim_quotient_eq P
  change ringKrullDim B = _ at hk
  rw [hm, hk] at hform hdrop
  rw [hm]
  change _ = ringKrullDim B
  rw [hk]
  have hne : W'.height ≠ ⊤ := ne_top_of_le_ne_top ENat.one_ne_top hht
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hh] at hform hht
  have h1 : h ≤ 1 := by exact_mod_cast hht
  have h2 : h + m = k := by exact_mod_cast hform
  have h3 : m + 1 ≤ k := by exact_mod_cast hdrop
  have : m + 1 = k := by omega
  rw [← this]
  push_cast
  rfl

end SectionComponents


open SectionComponents in
theorem SectionComponents.proof_closed : SectionComponents.Statement := by
  intro F _ n J f hequi hf

  have fwd : ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes → W ∈ (J ⊔ Ideal.span {f}).minimalPrimes := by
    intro P hP W hW
    have _ : P.IsPrime := hP.1.1
    have _ : W.IsPrime := hW.1.1
    refine ⟨⟨hW.1.1, sup_le_sup_right hP.1.2 _ |>.trans hW.1.2⟩, ?_⟩
    rintro Q ⟨hQ, hJQ⟩ hQW
    obtain ⟨P', hP', hP'Q⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hJQ)
    have _ : P'.IsPrime := hP'.1.1
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hP'Q (le_sup_right.trans hJQ) : P' ⊔ Ideal.span {f} ≤ Q)
    have _ : W'.IsPrime := hW'.1.1
    have hW'W : W' ≤ W := hW'Q.trans hQW
    suffices W' = W by rw [← this]; exact hW'Q
    by_contra hne
    have hlt := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW'W hne)
    rw [ringKrullDim_quotient_add_one_eq (hf P hP) hW, hequi P hP P' hP',
      ← ringKrullDim_quotient_add_one_eq (hf P' hP') hW'] at hlt
    obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq W'
    rw [hm] at hlt
    have : m + 1 ≤ m := by exact_mod_cast hlt
    omega
  intro P hP W
  refine ⟨fun hW => ⟨fwd P hP W hW, le_sup_left.trans hW.1.2⟩, ?_⟩
  rintro ⟨hW, hPW⟩
  have _ : W.IsPrime := hW.1.1
  obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW (le_sup_right.trans hW.1.2) : P ⊔ Ideal.span {f} ≤ W)
  have heq : W = W' := le_antisymm (hW.2 (fwd P hP W' hW').1 hW'W) hW'W
  rwa [heq]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : NullMeasurableSet s μ) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ = ∫⁻ y in f '' s, g y ∂μ := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have himg : f '' t =ᵐ[μ] f '' s := by
    have hst : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [hst, image_union]
    refine (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ (fun x hx ↦ ?_)
      (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  rw [setLIntegral_congr t_eq_s.symm, ← setLIntegral_congr himg,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht (fun x hx => (hf' x (ts hx)).mono ts)
      (hf.mono ts)]
  congr 1
  funext x
  exact mul_comm _ _

theorem AreaMultiplicityWeight.proof : AreaMultiplicityWeight.Statement := by
  intro E _ _ _ _ _ μ _ A f f' hA hf'
  classical
  set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hB : NullMeasurableSet B μ := by
    obtain ⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A) :=
      ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
        (aemeasurable_fderivWithin μ hA hf')
    refine (hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_
    filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx
    change (x ∈ A ∩ d ⁻¹' {0}ᶜ) ↔ (x ∈ B)
    by_cases hxA : x ∈ A
    · simp [B, hxA, hx hxA]
    · simp [B, hxA]

  have hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f'
      (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, NullMeasurableSet (P n) μ := fun n => hB.inter (htm n).nullMeasurableSet
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPA n hx)).mono (hPA n)
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, NullMeasurableSet (f '' P n) μ := fun n =>
    nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)

  have hNae : ∀ᵐ y ∂μ, ∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y =
      (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxA, hxy⟩
        have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
        exact ⟨n, ⟨hxB, hn⟩, hxy⟩
      · rintro ⟨n, hxP, hxy⟩
        exact ⟨hPA n hxP, hxy⟩
    rw [hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _)
      (sep_subset _ _))]
    refine tsum_congr fun n => ?_
    by_cases hyn : y ∈ f '' P n
    · obtain ⟨x, hx, rfl⟩ := hyn
      have hs : {z ∈ P n | f z = f x} = {x} := by
        ext z
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
      rw [hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]
      simp
    · have hs : {z ∈ P n | f z = y} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hz e => hyn ⟨z, hz, e⟩
      rw [hs, encard_empty]
      simp [hyn]
  refine ⟨(AEMeasurable.tsum fun n => aemeasurable_one.indicator₀ (himg n)).congr hNae,
    fun g hg => ?_⟩
  calc ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, ∫⁻ y in f '' P n, g y ∂μ := tsum_congr fun n =>
        AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ μ (hPm n) (hderP n) (hinj n) g
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator g y ∂μ :=
        tsum_congr fun n => (lintegral_indicator₀ (himg n) g).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator g y ∂μ :=
        (lintegral_tsum fun n => hg.aemeasurable.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y) * g y ∂μ := by
        congr 1; funext y
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        by_cases h : y ∈ f '' P n <;> simp [h]
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hNae] with y hy
        rw [hy]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Submodule
open scoped Pointwise

namespace LocalSectionLengthSum

theorem length_quot_smul_top_eq {B : Type*} [CommRing B] (I : Ideal B) (f : B) :
    Module.length B ((B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))) =
      Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by
  let g : B →ₗ[B] (B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I)) :=
    (f • ⊤ : Submodule B (B ⧸ I)).mkQ ∘ₗ I.mkQ
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker g = I ⊔ Ideal.span {f} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
      Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul] at hy
      have hx : x = f * b - (f * b - x) := by ring
      rw [hx]
      exact sub_mem (mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
        (mem_sup_left hy)
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have h : f * a - (y + a * f) = -y := by ring
      rw [h]
      exact neg_mem hy
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq]

theorem length_pi_quot_smul_top_eq {B ι : Type*} [CommRing B] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (f : B) :
    Module.length B ((Π i, M i) ⧸ (f • ⊤ : Submodule B (Π i, M i))) =
      ∑ i, Module.length B (M i ⧸ (f • ⊤ : Submodule B (M i))) := by
  let g : (Π i, M i) →ₗ[B] (Π i, M i ⧸ (f • ⊤ : Submodule B (M i))) :=
    LinearMap.pi fun i => (f • ⊤ : Submodule B (M i)).mkQ ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by simp [g, hx i]⟩
  have hker : LinearMap.ker g = f • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · intro h
      have hx : ∀ i, ∃ y : M i, f • y = x i := fun i => by
        have h' := congrFun h i
        simpa [g, mem_smul_pointwise_iff_exists] using h'
      choose y hy using hx
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      exact (Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul (y i) f ⊤ mem_top)
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq, Module.length_pi_of_fintype]

end LocalSectionLengthSum

theorem LocalSectionLengthSum.proof (hPi : PiQuotCokerFiniteLength.Statement) :
    LocalSectionLengthSum.Statement := by
  intro B _ _ _ J f hJ hf hQ
  obtain ⟨hinj, hfin⟩ := hPi B J hJ hQ
  have hfinite := J.finite_minimalPrimes_of_isNoetherianRing B
  let _ : Fintype J.minimalPrimes := hfinite.fintype
  have hreg : Function.Injective fun x : ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) => f • x := by
    intro x y hxy
    funext P
    have : (P : Ideal B).IsPrime := P.2.1.1
    have h : f • x P = f • y P := congrFun hxy P
    rw [Algebra.smul_def, Algebra.smul_def] at h
    refine mul_left_cancel₀ ?_ h
    rw [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf P P.2
  have e1 := Model.TorsionFreeQuotientLength.length_quot_smul_eq (quotToPiMinimalPrimes J) hinj
    hreg hfin
  rw [← LocalSectionLengthSum.length_quot_smul_top_eq J f, ← e1,
    LocalSectionLengthSum.length_pi_quot_smul_top_eq]
  simp_rw [LocalSectionLengthSum.length_quot_smul_top_eq]
  exact (Finset.sum_subtype (p := (· ∈ J.minimalPrimes)) hfinite.toFinset
    (fun P => hfinite.mem_toFinset)
    (fun P : Ideal B => Module.length B (B ⧸ (P ⊔ Ideal.span {f})))).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def ConeFiniteFibreDim.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ m

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def ConeKrullDimLe.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ m

end

end GroundTheory.Heights₂.Heights
end
