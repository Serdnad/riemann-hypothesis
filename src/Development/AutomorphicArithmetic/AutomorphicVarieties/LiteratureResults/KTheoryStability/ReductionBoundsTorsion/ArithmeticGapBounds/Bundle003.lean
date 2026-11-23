module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Bundle001
public import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.UnfoldA

open PositivityTheory.KB.SpectralGap

variable {Λ S : Type} [Group Λ] [Group S]

abbrev RQ (B K : Subgroup Λ) := Quotient (QuotientGroup.rightRel (B.subgroupOf K))

theorem card_Q (B K : Subgroup Λ) : Nat.card (RQ B K) = (B.subgroupOf K).index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)

theorem finite_Q (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) : Finite (RQ B K) := by
  have h : Nat.card (RQ B K) ≠ 0 := by rw [card_Q]; exact hi
  exact (Nat.card_ne_zero.mp h).2

theorem avg_eq_sum (j : Λ →* S) (B K : Subgroup Λ) [Fintype (RQ B K)] (u : S → ℝ) (x : S) :
    avg j B K u x = ((B.subgroupOf K).index : ℝ)⁻¹ *
      ∑ c : RQ B K, u (j ((c.out : K) : Λ) * x) := by
  rw [avg, finsum_eq_sum_of_fintype]

theorem mk_eq_iff {B K : Subgroup Λ} (a b : K) :
    Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) a = Quotient.mk _ b ↔
      (b : Λ) * (a : Λ)⁻¹ ∈ B := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply.trans (by rw [Subgroup.mem_subgroupOf]; simp)

theorem out_mk {B K : Subgroup Λ} (k : K) :
    (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ) * (k : Λ)⁻¹ ∈ B := by
  have h : Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K))
      (Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out = Quotient.mk _ k :=
    Quotient.out_eq _
  rw [mk_eq_iff] at h
  simpa [mul_inv_rev] using B.inv_mem h

theorem linv_out {j : Λ →* S} {B K : Subgroup Λ} {u : S → ℝ} (hu : LInv j B u) (k : K) (x : S) :
    u (j (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ) * x) =
      u (j (k : Λ) * x) := by
  have h := out_mk (B := B) k
  set o : Λ := (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ)
  calc u (j o * x) = u (j (o * (k : Λ)⁻¹) * (j (k : Λ) * x)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
    _ = u (j (k : Λ) * x) := hu _ h _

theorem avg_linv (j : Λ →* S) (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ)
    (hu : LInv j B u) : LInv j K (avg j B K u) := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  intro γ hγ x
  rw [avg_eq_sum, avg_eq_sum]
  congr 1
  let g : K := ⟨γ, hγ⟩
  let e : RQ B K ≃ RQ B K := Quotient.congr (Equiv.mulRight g) (fun a b => by
    simp only [Equiv.coe_mulRight]
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply,
      show b * g * (a * g)⁻¹ = b * a⁻¹ by group])
  refine Fintype.sum_equiv e _ _ (fun c => ?_)
  have hc : e c = Quotient.mk _ (c.out * g) := by
    conv_lhs => rw [← Quotient.out_eq c]
    exact Quotient.congr_mk _ _ _
  rw [hc, linv_out hu, Subgroup.coe_mul, map_mul, mul_assoc]

theorem avg_of_linv (j : Λ →* S) (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ)
    (hu : LInv j K u) : avg j B K u = u := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  funext x
  rw [avg_eq_sum]
  have h : ∀ c : RQ B K, u (j ((c.out : K) : Λ) * x) = u x := fun c => hu _ (c.out : K).2 x
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_Q]
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hi) _

theorem avg_meas [MeasurableSpace S] [MeasurableMul S] (j : Λ →* S) (B K : Subgroup Λ)
    (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (hu : Measurable u) :
    Measurable (avg j B K u) := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  have h : avg j B K u = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ *
      ∑ c : RQ B K, u (j ((c.out : K) : Λ) * x) := funext (avg_eq_sum j B K u)
  rw [h]
  exact measurable_const.mul
    (Finset.measurable_sum _ fun c _ => hu.comp (measurable_const_mul _))

theorem avg_tower (j : Λ →* S) (B E K : Subgroup Λ) (hBE : B ≤ E) (hEK : E ≤ K)
    (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (hu : LInv j B u) :
    avg j E K (avg j B E u) = avg j B K u := by
  have hmul : (B.subgroupOf E).index * (E.subgroupOf K).index = (B.subgroupOf K).index :=
    Subgroup.relIndex_mul_relIndex B E K hBE hEK
  have hBEi : (B.subgroupOf E).index ≠ 0 := fun h => hi (by rw [← hmul, h, zero_mul])
  have hEKi : (E.subgroupOf K).index ≠ 0 := fun h => hi (by rw [← hmul, h, mul_zero])
  haveI := finite_Q B K hi
  haveI := finite_Q B E hBEi
  haveI := finite_Q E K hEKi
  letI := Fintype.ofFinite (RQ B K)
  letI := Fintype.ofFinite (RQ B E)
  letI := Fintype.ofFinite (RQ E K)
  let φ : RQ E K × RQ B E → RQ B K := fun p => Quotient.mk _
    (⟨((p.2.out : E) : Λ) * ((p.1.out : K) : Λ), K.mul_mem (hEK (p.2.out : E).2) (p.1.out : K).2⟩ : K)
  have hinj : Function.Injective φ := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ h
    have h1 := (mk_eq_iff _ _).mp h
    simp only at h1
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c', mk_eq_iff]
      have : ((c'.out : K) : Λ) * ((c.out : K) : Λ)⁻¹ = ((d'.out : E) : Λ)⁻¹ *
          ((((d'.out : E) : Λ) * ((c'.out : K) : Λ)) * (((d.out : E) : Λ) * ((c.out : K) : Λ))⁻¹) *
          ((d.out : E) : Λ) := by group
      rw [this]
      exact E.mul_mem (E.mul_mem (E.inv_mem (d'.out : E).2) (hBE h1)) (d.out : E).2
    subst hc
    have hd : d = d' := by
      rw [← Quotient.out_eq d, ← Quotient.out_eq d', mk_eq_iff]
      have : ((d'.out : E) : Λ) * ((d.out : E) : Λ)⁻¹ =
          (((d'.out : E) : Λ) * ((c.out : K) : Λ)) * (((d.out : E) : Λ) * ((c.out : K) : Λ))⁻¹ := by
        group
      rw [this]; exact h1
    rw [hd]
  have hcard : Fintype.card (RQ E K × RQ B E) = Fintype.card (RQ B K) := by
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, card_Q, card_Q, card_Q, ← hmul, mul_comm]
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  funext x
  rw [avg_eq_sum j E K, avg_eq_sum j B K]
  simp_rw [avg_eq_sum j B E u]
  have hs : ∑ q : RQ B K, u (j ((q.out : K) : Λ) * x) =
      ∑ c : RQ E K, ∑ d : RQ B E, u (j ((d.out : E) : Λ) * (j ((c.out : K) : Λ) * x)) := by
    rw [← Fintype.sum_prod_type']
    refine (Fintype.sum_bijective φ hbij _ _ (fun p => ?_)).symm
    simp only [φ]
    rw [linv_out hu]
    dsimp only
    rw [map_mul, mul_assoc]
  rw [hs, ← Finset.mul_sum, ← hmul, Nat.cast_mul]
  ring

end PositivityTheory.KB.SpectralGap.UnfoldA

end
end

section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Pointwise

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] [MeasurableSpace S] (j : Λ →* S) (B : Subgroup Λ)
  (μ : Measure S) (DB : Set S)

abbrev Qt := Quotient (MulAction.orbitRel (B.map j) S)

def pr : S → Qt j B := Quotient.mk _

def nu : Measure (Qt j B) := (μ.restrict DB).map (pr j B)

abbrev HL := Lp ℝ 2 (nu j B μ DB)

def lift (u : S → ℝ) : Qt j B → ℝ := fun q => u q.out

def Good (u : S → ℝ) : Prop := Measurable u ∧ LInv j B u ∧ MemLp u 2 (μ.restrict DB)

variable {j B μ DB}

theorem linv_rel {u : S → ℝ} (hu : LInv j B u) {x y : S} (h : MulAction.orbitRel (B.map j) S x y) :
    u x = u y := by
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨⟨g, hg⟩, rfl⟩ := h
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  exact hu γ hγ y

theorem measurable_pr : Measurable (pr j B) := by
  exact measurable_quotient_mk''

theorem pr_mul {γ : Λ} (hγ : γ ∈ B) (x : S) : pr j B (j γ * x) = pr j B x := by
  unfold pr
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr ⟨⟨j γ, Subgroup.mem_map_of_mem j hγ⟩, rfl⟩

theorem lift_pr {u : S → ℝ} (hu : LInv j B u) (x : S) : lift j B u (pr j B x) = u x := by
  exact linv_rel hu (Quotient.mk_out' x)

theorem measurable_lift {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) : Measurable (lift j B u) := by
  refine measurable_from_quotient.mpr ?_
  have : (lift j B u ∘ Quotient.mk'') = u := funext fun x => lift_pr hu x
  rw [this]; exact hm

theorem memLp_lift {u : S → ℝ} (h : Good j B μ DB u) : MemLp (lift j B u) 2 (nu j B μ DB) := by
  obtain ⟨hm, hi, hmem⟩ := h
  unfold nu
  rw [memLp_map_measure_iff (measurable_lift hm hi).aestronglyMeasurable measurable_pr.aemeasurable]
  have : (lift j B u ∘ pr j B) = u := funext fun x => lift_pr hi x
  rw [this]; exact hmem


variable (j B μ DB) in
def cls (u : S → ℝ) : HL j B μ DB := by
  classical exact if h : Good j B μ DB u then (memLp_lift h).toLp (lift j B u) else 0

theorem good_iff {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) :
    Good j B μ DB u ↔ IntegrableOn (fun x => u x ^ 2) DB μ := by
  unfold Good
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact ⟨fun h => h.2.2, fun h => ⟨hm, hu, h⟩⟩

theorem good_sub {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    Good j B μ DB (fun x => u x - v x) := by
  refine ⟨hu.1.sub hv.1, fun γ hγ x => ?_, hu.2.2.sub hv.2.2⟩
  show u (j γ * x) - v (j γ * x) = u x - v x
  rw [hu.2.1 γ hγ x, hv.2.1 γ hγ x]

theorem cls_sub {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    cls j B μ DB (fun x => u x - v x) = cls j B μ DB u - cls j B μ DB v := by
  unfold cls
  rw [dite_eq_left (good_sub hu hv), dite_eq_left hu, dite_eq_left hv]
  exact MemLp.toLp_sub (memLp_lift hu) (memLp_lift hv)

theorem cls_inner {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    ⟪cls j B μ DB u, cls j B μ DB v⟫_ℝ = ∫ x in DB, u x * v x ∂μ := by
  unfold cls
  rw [dite_eq_left hu, dite_eq_left hv, L2.inner_def]
  have h1 := (memLp_lift hu).coeFn_toLp
  have h2 := (memLp_lift hv).coeFn_toLp
  have hcongr : (fun q => ⟪((memLp_lift hu).toLp (lift j B u) : Qt j B → ℝ) q,
      ((memLp_lift hv).toLp (lift j B v) : Qt j B → ℝ) q⟫_ℝ) =ᵐ[nu j B μ DB]
      fun q => lift j B u q * lift j B v q := by
    filter_upwards [h1, h2] with q hq1 hq2
    rw [hq1, hq2]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae hcongr]
  have hm : Measurable (fun q => lift j B u q * lift j B v q) :=
    (measurable_lift hu.1 hu.2.1).mul (measurable_lift hv.1 hv.2.1)
  unfold nu
  rw [integral_map measurable_pr.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [lift_pr hu.2.1, lift_pr hv.2.1]

theorem cls_norm_sq {u : S → ℝ} (hu : Good j B μ DB u) :
    ‖cls j B μ DB u‖ ^ 2 = ∫ x in DB, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, cls_inner hu hu]
  simp only [sq]

theorem cls_surj (f : HL j B μ DB) : ∃ u, Good j B μ DB u ∧ cls j B μ DB u = f := by
  have hf := (Lp.aestronglyMeasurable f).aemeasurable
  set g := hf.mk f with hgdef
  have hg : Measurable g := hf.measurable_mk
  have hfg : (f : Qt j B → ℝ) =ᵐ[nu j B μ DB] g := hf.ae_eq_mk
  have hinv : LInv j B (g ∘ pr j B) := fun γ hγ x => by
    show g (pr j B (j γ * x)) = g (pr j B x)
    rw [pr_mul hγ x]
  have hLg : MemLp g 2 (nu j B μ DB) := (Lp.memLp f).ae_eq hfg
  have hgood : Good j B μ DB (g ∘ pr j B) := by
    refine ⟨hg.comp measurable_pr, hinv, ?_⟩
    unfold nu at hLg
    exact (memLp_map_measure_iff hg.aestronglyMeasurable measurable_pr.aemeasurable).1 hLg
  refine ⟨g ∘ pr j B, hgood, ?_⟩
  have hl : lift j B (g ∘ pr j B) = g := funext fun q => by
    show g (Quotient.mk _ q.out) = g q
    rw [Quotient.out_eq]
  unfold cls
  rw [dite_eq_left hgood]
  apply Lp.ext
  filter_upwards [(memLp_lift hgood).coeFn_toLp, hfg] with q h1 h2
  rw [h1, hl, h2]

theorem cls_eq_iff {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    cls j B μ DB u = cls j B μ DB v ↔ u =ᵐ[μ.restrict DB] v := by
  unfold cls; rw [dite_eq_left hu, dite_eq_left hv, MemLp.toLp_eq_toLp_iff]
  unfold nu Filter.EventuallyEq
  rw [ae_map_iff measurable_pr.aemeasurable
    (measurableSet_eq_fun (measurable_lift hu.1 hu.2.1) (measurable_lift hv.1 hv.2.1))]
  simp only [lift_pr hu.2.1, lift_pr hv.2.1]

theorem countable_map [Countable Λ] : Countable (B.map j) := by
  have hc : ((B.map j : Subgroup S) : Set S).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  exact hc.to_subtype

theorem ae_spread [Countable Λ] [MeasurableMul S] [μ.IsMulLeftInvariant]
    (hD : IsFundamentalDomain (B.map j) DB μ) {u v : S → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hiu : LInv j B u) (hiv : LInv j B v) (h : u =ᵐ[μ.restrict DB] v) : u =ᵐ[μ] v := by
  haveI := countable_map (j := j) (B := B)
  have inv : ∀ w : S → ℝ, LInv j B w → ∀ (g : B.map j) (x : S), w (g • x) = w x :=
    fun w hw g x => linv_rel hw (by rw [MulAction.orbitRel_apply]; exact MulAction.mem_orbit x g)
  have htm : MeasurableSet {x | u x ≠ v x} := (measurableSet_eq_fun hu hv).compl
  have ht : ∀ g : B.map j, g • {x | u x ≠ v x} = {x | u x ≠ v x} := by
    intro g
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_setOf_eq]
    rw [inv u hiu g⁻¹ x, inv v hiv g⁻¹ x]
  have hts : μ ({x | u x ≠ v x} ∩ DB) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h
  exact ae_iff.2 (hD.measure_zero_of_invariant _ ht hts)

theorem ae_translate [MeasurableMul S] [μ.IsMulLeftInvariant] {u v : S → ℝ} (g : S)
    (h : u =ᵐ[μ] v) : (fun x => u (g * x)) =ᵐ[μ] fun x => v (g * x) := by
  exact (measurePreserving_mul_left μ g).quasiMeasurePreserving.ae_eq h

end PositivityTheory.KB.SpectralGap.PGap

end
end
