module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SecRankSpecialize

open Vertical

def secMap {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    SecAlg Q y →ₐ[R] SecAlg (Q.map (MvPolynomial.map (algebraMap R S))) (algebraMap R S ∘ y) :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId R S))
    (by rw [SecAlgFieldChange.secIdeal_map]; exact Ideal.le_comap_map)

theorem secMap_mk {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (p : MvPolynomial (Fin n) R) :
    secMap S Q y (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := rfl

theorem mem_maximalIdeal_smul_of_secMap_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    (κ : Type*) [Field κ] [Algebra R κ] (hsurj : Function.Surjective (algebraMap R κ)) {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (x : SecAlg Q y)
    (hx : secMap κ Q y x = 0) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (SecAlg Q y)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R := by
    have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  have hp : p ∈ secIdeal Q y ⊔ Ideal.map C (IsLocalRing.maximalIdeal R) := by
    rw [secMap_mk, Ideal.Quotient.eq_zero_iff_mem, SecAlgFieldChange.secIdeal_map,
      ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective _ (MvPolynomial.map_surjective _ hsurj),
      ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, hker] at hx
    exact hx
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (secIdeal Q y)) hp
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at hm
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  have he : (Ideal.Quotient.mk (secIdeal Q y)).comp C = algebraMap R (SecAlg Q y) :=
    RingHom.ext fun _ => rfl
  rwa [he] at hm

end SecRankSpecialize


open SecRankSpecialize in
theorem SecRankSpecialize.proof : SecRankSpecialize.Statement := by
  intro R K κ _ _ _ _ _ _ _ _ n e Q y hsurj hfin
  classical
  let ρ := secMap κ Q y
  let ι := secMap K Q y
  have hρ : Function.Surjective ρ := by
    intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ hsurj q
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have : Module.Finite R
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_surjective ρ.toLinearMap hρ
  have : Module.Finite κ
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_restrictScalars_finite R κ _
  let v := Module.finBasis κ
    (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))
  choose b hb using fun i => hρ (v i)

  have htop : Submodule.span R (Set.range b) = ⊤ := by
    refine top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) ?_)
    intro x _
    choose r hr using fun i => hsurj (v.repr (ρ x) i)
    have hsum : ∑ i, r i • ρ (b i) = ρ x := by
      conv_rhs => rw [← v.sum_repr (ρ x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, ← hr i, algebraMap_smul]
    have hz : ρ (x - ∑ i, r i • b i) = 0 := by

      rw [map_sub, map_sum]
      simp only [map_smul]
      rw [hsum, sub_self]
    have hm := mem_maximalIdeal_smul_of_secMap_eq_zero κ hsurj Q y _ hz
    have hx : x = ∑ i, r i • b i + (x - ∑ i, r i • b i) := by abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hm

  have hB : ∀ x, ι x ∈ Submodule.span K (Set.range fun i => ι (b i)) := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range b) := htop ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add u w _ _ hu hw => rw [map_add (f := _)]; exact Submodule.add_mem _ hu hw
    | smul c u _ hu => rw [map_smul, ← algebraMap_smul K]; exact Submodule.smul_mem _ _ hu
  have hspan : Submodule.span K (Set.range fun i => ι (b i)) = ⊤ := by
    refine eq_top_iff.mpr fun z hz => ?_
    clear hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on' with
    | monomial u a =>
      have hmon : (Ideal.Quotient.mk _ (monomial u a) :
          Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) =
          a • ι (Ideal.Quotient.mk _ (monomial u 1)) := by
        rw [secMap_mk, MvPolynomial.map_monomial, map_one, ← Ideal.Quotient.mkₐ_eq_mk K,
          ← map_smul, smul_monomial, smul_eq_mul, mul_one]
      rw [hmon]
      exact Submodule.smul_mem _ _ (hB _)
    | add p q hp hq => rw [map_add (f := _)]; exact Submodule.add_mem _ hp hq
  calc Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y))
        = Module.finrank K (Submodule.span K (Set.range fun i => ι (b i))) := by
          rw [hspan, finrank_top]
      _ ≤ Fintype.card (Fin (Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)))) :=
          finrank_range_le_card _
      _ = _ := Fintype.card_fin _

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

theorem IsChowFormCycle.ne_zero {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  refine mul_ne_zero ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]; exact hc
  · rw [Finset.prod_ne_zero_iff]
    intro W hW
    exact pow_ne_zero _ (hg W hW).1

theorem DefectAverage.proof (h1 : MahlerAverageSplit.Statement) (h2 : CycleAverage.Statement) :
    DefectAverage.Statement := by
  intro n e δ h Z f hZ
  obtain ⟨hi1, hm1⟩ := h1 n e δ h f hZ.chow.ne_zero hZ.homog
  obtain ⟨hi2, hm2⟩ := h2 n e δ h Z f hZ
  have hi : IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) := by
    unfold mahlerDefect; exact hi1.sub hi2
  refine ⟨hi, ?_⟩
  have hsub : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) =
      (⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))) -
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) := by
    simp only [setAverage_eq, mahlerDefect]
    rw [integral_sub hi1 hi2, smul_sub]
  rw [hsub, ← hm1, hm2]
  ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem linForm_const_mul (c : ℂ) (v : Fin n → ℂ) :
    linForm (fun j => c * v j) = C c * linForm v := by
  simp only [linForm, Finset.mul_sum, map_mul, mul_assoc]

theorem HermNorm.norm_ne_zero (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : h.norm v ≠ 0 := by
  intro h0
  apply hv
  have hs : ∑ i, ‖(h.mat *ᵥ v) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)).mp h0
  have hm : h.mat *ᵥ v = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖(h.mat *ᵥ v) i‖)).mp hs i
      (Finset.mem_univ i)
    simpa using this
  exact Matrix.eq_zero_of_mulVec_eq_zero h.isUnit_det.ne_zero hm

theorem IsAdmissible.nrmv (h : HermNorm n) {Z : ProjCycle ℂ n} {v : Fin n → ℂ}
    (hv : IsAdmissible Z v) : IsAdmissible Z (nrmv h v) := by
  intro W hW hmem
  apply hv W hW
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hv W hW
    simp [linForm]
  have hc : ((h.norm v : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (h.norm_ne_zero hv0))
  have hmem' : C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v ∈ W := by
    rw [← linForm_const_mul]; exact hmem
  have : linForm v = C (((h.norm v : ℝ) : ℂ)⁻¹)⁻¹ * (C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [this]
  exact W.mul_mem_left _ hmem'

theorem AdmissibleAENrm.proof (h1 : AdmissibleAE.Statement) : AdmissibleAENrm.Statement := by
  intro n h Z hrel
  exact ae_restrict_of_ae ((h1 n Z hrel).mono fun v hv => hv.nrmv h)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

theorem ConeFubini.proof (h1 : BallVolume.Statement) : ConeFubini.Statement := by
  intro n h μ _ F c M hF hy
  obtain ⟨hpos, hfin⟩ := h1 n h
  have : IsFiniteMeasure (volume.restrict (ballH h)) := isFiniteMeasure_restrict.2 hfin.ne
  have hsm : StronglyMeasurable (Function.uncurry F) := hF.stronglyMeasurable

  have hint : Integrable (Function.uncurry F) ((volume.restrict (ballH h)).prod μ) := by
    rw [integrable_prod_iff' hsm.aestronglyMeasurable]
    refine ⟨hy.mono fun y hy => hy.1, ?_⟩
    refine Integrable.of_bound ?_ M ?_
    · exact (hsm.norm.integral_prod_left' (μ := volume.restrict (ballH h))).aestronglyMeasurable
    · filter_upwards [hy] with y hy
      have e : ∀ x, ‖Function.uncurry F (x, y)‖ = |F x y| := fun x => Real.norm_eq_abs _
      simp only [e]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact hy.2.1
  refine ⟨hint.integral_prod_left, ?_⟩
  have hvol : (volume (ballH h)).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  have hreal : volume.real (ballH h) = (volume (ballH h)).toReal := rfl

  have hin : ∀ᵐ y ∂μ, ∫ v in ballH h, F v y = c * (volume (ballH h)).toReal := by
    filter_upwards [hy] with y hy
    have e := hy.2.2
    rw [setAverage_eq, hreal, smul_eq_mul] at e
    field_simp at e ⊢
    linarith
  have hswap := integral_integral_swap hint
  rw [setAverage_eq, hreal, smul_eq_mul, hswap, integral_congr_ae hin, integral_const, smul_eq_mul]
  simp only [measureReal_def]
  field_simp
end
end Heights
end Heights₂
end GroundTheory
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormCycleAdd.proof (h1 : ChowFormAssoc.Statement) : ChowFormCycleAdd.Statement := by
  classical
  intro F _ n k Z₁ Z₂ f₁ f₂ ⟨c₁, hc₁, g₁, hg₁, hf₁⟩ ⟨c₂, hc₂, g₂, hg₂, hf₂⟩
  subst hf₁ hf₂
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F :=
    fun W => if W ∈ Z₁.support then g₁ W else g₂ W
  have hd : ∀ W, ∃ d : F, d ≠ 0 ∧ (W ∈ Z₂.support → g₂ W = C d * g W) := by
    intro W
    by_cases hW1 : W ∈ Z₁.support
    · by_cases hW2 : W ∈ Z₂.support
      · obtain ⟨d, hd, he⟩ := h1 F n k W (g₁ W) (g₂ W) (hg₁ W hW1) (hg₂ W hW2)
        exact ⟨d, hd, fun _ => by simp only [g, if_pos hW1, he]⟩
      · exact ⟨1, one_ne_zero, fun h => absurd h hW2⟩
    · exact ⟨1, one_ne_zero, fun _ => by simp only [g, if_neg hW1, map_one, one_mul]⟩
  choose d hd0 hdg using hd
  have hsupp : (Z₁ + Z₂).support = Z₁.support ∪ Z₂.support := by
    ext W
    simp only [Finsupp.mem_support_iff, Finset.mem_union, Finsupp.coe_add, Pi.add_apply, ne_eq,
      Nat.add_eq_zero_iff, not_and_or]
  refine ⟨c₁ * c₂ * ∏ W ∈ Z₂.support, d W ^ Z₂ W, ?_, g, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hc₁ hc₂)
      (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (hd0 W))
  · intro W hW
    rw [hsupp, Finset.mem_union] at hW
    by_cases hW1 : W ∈ Z₁.support
    · simpa only [g, if_pos hW1] using hg₁ W hW1
    · simpa only [g, if_neg hW1] using hg₂ W (hW.resolve_left hW1)
  · have e1 : ∏ W ∈ Z₁.support, g₁ W ^ Z₁ W =
        ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₁ W := by
      rw [← Finset.prod_subset Finset.subset_union_left (f := fun W => g W ^ Z₁ W)]
      · exact Finset.prod_congr rfl fun W hW => by simp only [g, if_pos hW]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    have e2 : ∏ W ∈ Z₂.support, g₂ W ^ Z₂ W =
        C (∏ W ∈ Z₂.support, d W ^ Z₂ W) * ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₂ W := by
      rw [← Finset.prod_subset Finset.subset_union_right (f := fun W => g W ^ Z₂ W)]
      · rw [map_prod, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun W hW => by rw [hdg W hW, mul_pow, map_pow]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    rw [hsupp, e1, e2]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib, map_mul]
    ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

namespace AdmissibleAE

variable {n : ℕ}

def formsIn (W : Ideal (MvPolynomial (Fin n) ℂ)) : Submodule ℝ (Fin n → ℂ) where
  carrier := {u | linForm u ∈ W}
  zero_mem' := by simp [linForm]
  add_mem' := by
    intro a b ha hb
    have : linForm (a + b) = linForm a + linForm b := by
      simp [linForm, Finset.sum_add_distrib, add_mul]
    simp only [Set.mem_ofPred_eq, this] at ha hb ⊢
    exact W.add_mem ha hb
  smul_mem' := by
    intro c u hu
    have : linForm (c • u) = C (c : ℂ) * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, Complex.real_smul]
    simp only [Set.mem_ofPred_eq, this] at hu ⊢
    exact W.mul_mem_left _ hu

theorem linForm_single (j : Fin n) :
    linForm (Pi.single j (1 : ℂ)) = (X j : MvPolynomial (Fin n) ℂ) := by
  simp [linForm, Pi.single_apply]

theorem formsIn_ne_top {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsRelevant W) : formsIn W ≠ ⊤ := by
  obtain ⟨j, hj⟩ := hW
  intro htop
  have hmem : Pi.single j (1 : ℂ) ∈ formsIn W := htop ▸ Submodule.mem_top
  exact hj (linForm_single j ▸ hmem)

end AdmissibleAE


open AdmissibleAE in
theorem AdmissibleAE.proof : AdmissibleAE.Statement := by
  intro n Z hrel
  unfold IsAdmissible
  refine (Filter.eventually_all_finset _).2 fun W hW => ?_
  rw [ae_iff]
  have hnull : volume (formsIn W : Set (Fin n → ℂ)) = 0 :=
    Measure.addHaar_submodule volume _ (formsIn_ne_top (hrel W hW))
  simp only [not_not]
  exact hnull

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem BallVolume.proof : BallVolume.Statement := by
  intro n h
  have hcont : Continuous fun v : Fin n → ℂ => h.norm v := by
    simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
    fun_prop
  have hopen : IsOpen (ballH h) := isOpen_lt hcont continuous_const
  have hzero : (0 : Fin n → ℂ) ∈ ballH h := by
    show h.norm 0 < 1
    simp [HermNorm.norm]
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbdd : Bornology.IsBounded (ballH h) := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℂ))
      (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    intro j
    exact norm_le_of_hermNorm_lt h hv j
  exact ⟨hopen.measure_pos volume ⟨0, hzero⟩, hbdd.measure_lt_top⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem FsLogPointOf.proof : FsLogPointOf.Statement := by
  intro n h v y
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hd : h.dualNorm (h.pointOf y) = (HermNorm.std n).dualNorm (fun i => y i) := by
    simp only [HermNorm.dualNorm, HermNorm.pointOf, HermNorm.std, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.transpose_one, inv_one]
  have hn : (HermNorm.std n).norm (h.mat *ᵥ v) = h.norm v := by
    simp only [HermNorm.norm, HermNorm.std, Matrix.one_mulVec]
  have hs : ∑ j, v j * h.pointOf y j = ∑ i, (h.mat *ᵥ v) i * y i := by
    have := Matrix.dotProduct_mulVec v h.matᵀ (fun i => y i)
    rw [Matrix.vecMul_transpose] at this
    simpa [dotProduct, HermNorm.pointOf] using this
  unfold fsLog nrmv
  rw [hd, hn]
  simp only [mul_assoc, ← Finset.mul_sum, hs]

end GroundTheory.Heights₂.Heights
end
