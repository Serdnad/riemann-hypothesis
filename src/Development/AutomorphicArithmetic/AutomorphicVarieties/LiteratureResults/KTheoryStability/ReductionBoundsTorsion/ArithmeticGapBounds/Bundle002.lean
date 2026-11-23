module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Bundle001
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Chebyshev
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Dynamics.Ergodic.Action.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S)

theorem linv_mono {E E' : Subgroup Λ} (h : E ≤ E') {u : S → ℝ} (hu : LInv j E' u) : LInv j E u :=
  fun γ hγ x => hu γ (h hγ) x

theorem linv_sub {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x - v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

theorem linv_mul {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x * v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

theorem linv_sq {E : Subgroup Λ} {u : S → ℝ} (hu : LInv j E u) : LInv j E (fun x => u x ^ 2) := by
  intro γ hγ x
  simp only [hu γ hγ x]

variable {B K : Subgroup Λ}

theorem card_cosets :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

theorem finite_cosets (h : (B.subgroupOf K).index ≠ 0) :
    Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
  Nat.finite_of_card_ne_zero (by rw [card_cosets]; exact h)

theorem avg_sub (h : (B.subgroupOf K).index ≠ 0) (u v : S → ℝ) (x : S) :
    avg j B K (fun y => u y - v y) x = avg j B K u x - avg j B K v x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, mul_sub]

theorem avg_mul_left {a : S → ℝ} (ha : LInv j K a) (b : S → ℝ) (x : S) :
    avg j B K (fun y => a y * b y) x = a x * avg j B K b x := by
  by_cases h : (B.subgroupOf K).index = 0
  · simp [avg, h]
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype]
  have hc : ∀ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)),
      a (j (c.out : Λ) * x) * b (j (c.out : Λ) * x) = a x * b (j (c.out : Λ) * x) := by
    intro c
    rw [ha _ c.out.2 x]
  simp only [hc, ← Finset.mul_sum]
  ring

theorem avg_nonneg {u : S → ℝ} (hu : ∀ y, 0 ≤ u y) (x : S) : 0 ≤ avg j B K u x := by
  unfold avg
  apply mul_nonneg
  · positivity
  · exact finsum_nonneg fun c => hu _

theorem avg_sq_le (h : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (x : S) :
    avg j B K u x ^ 2 ≤ avg j B K (fun y => u y ^ 2) x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  have hc : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card
      = (B.subgroupOf K).index := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_cosets]
  have hn : (0 : ℝ) < (B.subgroupOf K).index := by exact_mod_cast Nat.pos_of_ne_zero h
  simp only [avg, finsum_eq_sum_of_fintype]
  have key := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) => u (j (c.out : Λ) * x))
  rw [hc] at key
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn_def
  set s := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x)
  set t := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x) ^ 2
  calc (n⁻¹ * s) ^ 2 = n⁻¹ ^ 2 * s ^ 2 := by ring
    _ ≤ n⁻¹ ^ 2 * (n * t) := by gcongr
    _ = n⁻¹ * t := by
      field_simp

end PositivityTheory.KB.SpectralGap.PGap

end
end

section

open MeasureTheory Filter Set
open scoped symmDiff Topology ENNReal

namespace PositivityTheory.KB.SpectralGap

namespace AlmostEverywhereConstant

variable {S : Type} [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
  [SecondCountableTopology S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
  (μ : Measure S) [μ.IsHaarMeasure]

def tr (g : S) : C(S, S) := ⟨(g * ·), continuous_const_mul g⟩

theorem coe_tr (g : S) : ⇑(tr g) = (g * ·) := rfl

theorem continuous_tr : Continuous (tr : S → C(S, S)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_mul

theorem tendsto_pre {x : ℕ → S} {g : S} (hx : Tendsto x atTop (𝓝 g)) {P : Set S}
    (hP : MeasurableSet P) (hμP : μ P ≠ ∞) :
    Tendsto (fun n => μ (((x n * ·) ⁻¹' P) ∆ ((g * ·) ⁻¹' P))) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => tr (x n)) atTop (𝓝 (tr g)) := (continuous_tr.tendsto g).comp hx
  have key := tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) hc
    (Eventually.of_forall fun n => measurePreserving_mul_left μ (x n))
    (measurePreserving_mul_left μ g) hP.nullMeasurableSet hμP
  simpa only [coe_tr] using key

theorem isClosed_stab {T : Set S} (hT : MeasurableSet T) :
    IsClosed {g : S | (g * ·) ⁻¹' T =ᵐ[μ] T} := by
  apply isClosed_of_closure_subset
  intro g hg
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.1 hg
  show (g * ·) ⁻¹' T =ᵐ[μ] T
  rw [← measure_symmDiff_eq_zero_iff]
  have key : ∀ K : Set S, IsCompact K → μ ((((g * ·) ⁻¹' T) ∆ T) ∩ K) = 0 := by
    intro K hK
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds g
    set L : Set S := (fun p : S × S => p.1 * p.2) '' (N ×ˢ K) with hLdef
    have hLc : IsCompact L := (hNc.prod hK).image continuous_mul
    have hPm : MeasurableSet (T ∩ L) := hT.inter hLc.measurableSet
    have hPf : μ (T ∩ L) ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt hLc.measure_lt_top).ne
    have ev : ∀ᶠ n in atTop, x n ∈ N := hx hN
    have tend := tendsto_pre μ hx hPm hPf
    refine le_antisymm ?_ bot_le
    apply ge_of_tendsto tend
    filter_upwards [ev] with n hn
    have h0 : μ (((x n * ·) ⁻¹' T) ∆ T) = 0 := measure_symmDiff_eq_zero_iff.2 (hxS n)
    have hsub : (((g * ·) ⁻¹' T) ∆ T) ∩ K ⊆
        (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) ∪ (((x n * ·) ⁻¹' T) ∆ T) := by
      rintro y ⟨hyD, hyK⟩
      have h1 : x n * y ∈ L := ⟨(x n, y), ⟨hn, hyK⟩, rfl⟩
      have h2 : g * y ∈ L := ⟨(g, y), ⟨mem_of_mem_nhds hN, hyK⟩, rfl⟩
      simp only [Set.mem_union, Set.mem_symmDiff, Set.mem_preimage, Set.mem_inter_iff, h1, h2,
        and_true] at hyD ⊢
      tauto
    calc μ ((((g * ·) ⁻¹' T) ∆ T) ∩ K)
        ≤ μ ((((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) ∪ (((x n * ·) ⁻¹' T) ∆ T)) :=
          measure_mono hsub
      _ ≤ μ (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) + μ (((x n * ·) ⁻¹' T) ∆ T) :=
          measure_union_le _ _
      _ = μ (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) := by rw [h0, add_zero]
  have hD : ((g * ·) ⁻¹' T) ∆ T = ⋃ n, ((((g * ·) ⁻¹' T) ∆ T) ∩ compactCovering S n) := by
    rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
  rw [hD]
  exact measure_iUnion_null fun n => key _ (isCompact_compactCovering S n)

theorem aeconst_set {A : Subgroup S} (hA : Dense (A : Set S)) {T : Set S} (hT : MeasurableSet T)
    (h : ∀ g ∈ A, (g * ·) ⁻¹' T =ᵐ[μ] T) : EventuallyEmptyOrUniv T (ae μ) := by
  have hcl : closure (A : Set S) ⊆ {g : S | (g * ·) ⁻¹' T =ᵐ[μ] T} :=
    closure_minimal (fun g hg => h g hg) (isClosed_stab μ hT)
  rw [hA.closure_eq] at hcl
  exact aeconst_of_forall_preimage_smul_ae_eq S hT.nullMeasurableSet fun g => hcl (mem_univ g)

end AlmostEverywhereConstant

theorem aeConst_holds : AEConst := by
  intro S _ _ _ _ _ _ _ _ μ _ A hA u hu hinv
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet ?_
  intro U hU
  have hT : MeasurableSet (u ⁻¹' U) := hu hU
  have key := AlmostEverywhereConstant.aeconst_set μ hA hT fun g hg => by
    filter_upwards [hinv g hg] with x hx
    show u (g * x) ∈ U ↔ u x ∈ U
    rw [hx]
  exact eventuallyEmptyOrUniv_iff.1 key

end PositivityTheory.KB.SpectralGap
end

section

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace PositivityTheory.KB.SpectralGap.UnfoldB

open PositivityTheory.KB.SpectralGap

def rep {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ)
    (c : Quotient (QuotientGroup.rightRel (B.subgroupOf K))) : S :=
  j ((c.out : K) : Λ)

theorem card_quot {Λ : Type} [Group Λ] (B K : Subgroup Λ) :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

theorem countable_map {Λ S : Type} [Group Λ] [Countable Λ] [Group S] (j : Λ →* S) (K : Subgroup Λ) :
    Countable (K.map j) := by
  have : ((K.map j : Subgroup S) : Set S).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  exact this.to_subtype

theorem rep_ex {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ) :
    ∀ g ∈ K.map j, ∃ h ∈ B.map j, ∃ c, g = h * rep j B K c := by
  rintro g ⟨k, hk, rfl⟩
  let c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) := Quotient.mk _ ⟨k, hk⟩
  have hr : QuotientGroup.rightRel (B.subgroupOf K) c.out ⟨k, hk⟩ := Quotient.mk_out _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at hr
  refine ⟨j (k * ((c.out : K) : Λ)⁻¹), ⟨_, ?_, rfl⟩, c, ?_⟩
  · simpa using hr
  · simp [rep]

theorem rep_inj {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (hj : Function.Injective j)
    (B K : Subgroup Λ) :
    ∀ h ∈ B.map j, ∀ h' ∈ B.map j, ∀ c c', h * rep j B K c = h' * rep j B K c' → c = c' := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ c c' heq
  rw [rep, rep, ← map_mul, ← map_mul] at heq
  have e := hj heq
  rw [← Quotient.out_equiv_out]
  show QuotientGroup.rightRel (B.subgroupOf K) c.out c'.out
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  have key : ((c'.out : K) : Λ) * ((c.out : K) : Λ)⁻¹ = b'⁻¹ * b := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e]
    group
  simpa [key] using B.mul_mem (B.inv_mem hb') hb

theorem unfold_fd (Λ S : Type) [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S]
    [MeasurableMul S] (μ : Measure S) [μ.IsMulLeftInvariant] (j : Λ →* S) (hj : Function.Injective j)
    (B K : Subgroup Λ) (hBK : B ≤ K) (hi : (B.subgroupOf K).index ≠ 0) :
    ∀ D : Set S, IsFundamentalDomain (K.map j) D μ →
    (∃ D' : Set S, IsFundamentalDomain (B.map j) D' μ) ∧
    ∀ D' : Set S, IsFundamentalDomain (B.map j) D' μ → μ D' = (B.subgroupOf K).index * μ D ∧
      ∀ u : S → ℝ, Measurable u → LInv j B u →
        (IntegrableOn u D' μ ↔ IntegrableOn (avg j B K fun y => |u y|) D μ) ∧
        (IntegrableOn u D' μ → IntegrableOn (avg j B K u) D μ ∧
          ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, avg j B K u x ∂μ) := by
  intro D hD
  haveI : Countable (K.map j) := countable_map j K
  haveI : Countable (B.map j) := countable_map j B
  haveI : Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
    Nat.finite_of_card_ne_zero (by rw [card_quot]; exact hi)
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  have hrepΓ : ∀ c, rep j B K c ∈ K.map j := fun c => ⟨((c.out : K) : Λ), c.out.2, rfl⟩
  have hBK' : B.map j ≤ K.map j := Subgroup.map_mono hBK
  have hn : ((B.subgroupOf K).index : ℝ) ≠ 0 := by exact_mod_cast hi
  have hcard : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card
      = (B.subgroupOf K).index := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_quot]
  have hmp : ∀ a : S, MeasurePreserving (fun x => a • x) μ μ := fun a => measurePreserving_smul a μ
  have hemb : ∀ a : S, MeasurableEmbedding (fun x : S => a • x) :=
    fun a => measurableEmbedding_const_smul a
  have havg : ∀ (f : S → ℝ) (x : S), avg j B K f x
      = ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, f (rep j B K c * x) := by
    intro f x
    simp only [avg, finsum_eq_sum_of_fintype]
    rfl
  set D0 : Set S := ⋃ c, rep j B K c • D with hD0def
  have hmeasc : ∀ c, NullMeasurableSet (rep j B K c • D) μ := fun c =>
    hD.nullMeasurableSet_smul (⟨rep j B K c, hrepΓ c⟩ : K.map j)
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun c => rep j B K c • D) := by
    intro c c' hcc'
    have hne : (⟨rep j B K c, hrepΓ c⟩ : K.map j) ≠ ⟨rep j B K c', hrepΓ c'⟩ := by
      intro h
      apply hcc'
      have e := congrArg Subtype.val h
      exact rep_inj j hj B K 1 (one_mem _) 1 (one_mem _) c c' (by simpa using e)
    exact hD.aedisjoint hne
  have hD0 : IsFundamentalDomain (B.map j) D0 μ := by
    refine ⟨NullMeasurableSet.iUnion hmeasc, ?_, ?_⟩
    · filter_upwards [hD.ae_covers] with x hx
      obtain ⟨g, hg⟩ := hx
      obtain ⟨h, hh, c, hgc⟩ := rep_ex j B K ((g : S)⁻¹) (inv_mem g.2)
      refine ⟨⟨h⁻¹, inv_mem hh⟩, Set.mem_iUnion.2 ⟨c, ?_⟩⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      have e : (rep j B K c)⁻¹ * h⁻¹ = (g : S) := by
        rw [← mul_inv_rev, ← hgc, inv_inv]
      convert hg using 1
      show (rep j B K c)⁻¹ * (h⁻¹ * x) = (g : S) * x
      rw [← mul_assoc, e]
    · intro δ δ' hδ
      show AEDisjoint μ ((δ : S) • D0) ((δ' : S) • D0)
      rw [hD0def, Set.smul_set_iUnion, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff]
      intro c
      rw [AEDisjoint.iUnion_right_iff]
      intro c'
      rw [smul_smul, smul_smul]
      have h1 : (δ : S) * rep j B K c ∈ K.map j := mul_mem (hBK' δ.2) (hrepΓ c)
      have h2 : (δ' : S) * rep j B K c' ∈ K.map j := mul_mem (hBK' δ'.2) (hrepΓ c')
      have hne : (⟨_, h1⟩ : K.map j) ≠ ⟨_, h2⟩ := by
        intro h
        have e := congrArg Subtype.val h
        have hc := rep_inj j hj B K _ δ.2 _ δ'.2 c c' e
        subst hc
        exact hδ (Subtype.ext (mul_right_cancel e))
      exact hD.aedisjoint hne
  refine ⟨⟨D0, hD0⟩, fun D' hD' => ⟨?_, fun u hu hinv => ?_⟩⟩
  · rw [hD'.measure_eq hD0, ← setLIntegral_one, hD0def, lintegral_iUnion₀ hmeasc hdisj, tsum_fintype]
    simp only [setLIntegral_one]
    have hmc : ∀ c, μ (rep j B K c • D) = μ D := fun c => measure_smul μ (rep j B K c) D
    simp only [hmc, Finset.sum_const, hcard, nsmul_eq_mul]
  · have hinvΔ : ∀ (δ : B.map j) (x : S), u (δ • x) = u x := by
      rintro ⟨_, b, hb, rfl⟩ x
      exact hinv b hb x
    have hI : IntegrableOn u D' μ ↔ IntegrableOn u D0 μ := hD'.integrableOn_iff hD0 hinvΔ
    have hIc : IntegrableOn u D0 μ ↔ ∀ c, IntegrableOn (fun x => u (rep j B K c * x)) D μ := by
      rw [hD0def, integrableOn_finite_iUnion]
      exact forall_congr' fun c => (hmp _).integrableOn_image (hemb _)
    have hm : ∀ c, Measurable (fun x => u (rep j B K c * x)) := fun c =>
      hu.comp (measurable_const_mul _)
    have hAbs : IntegrableOn (avg j B K fun y => |u y|) D μ ↔
        ∀ c, IntegrableOn (fun x => u (rep j B K c * x)) D μ := by
      constructor
      · intro h c
        have h2 : IntegrableOn (fun x => ((B.subgroupOf K).index : ℝ) *
            avg j B K (fun y => |u y|) x) D μ := h.const_mul _
        refine Integrable.mono' h2 (hm c).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [havg, Real.norm_eq_abs, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
        exact Finset.single_le_sum (f := fun c => |u (rep j B K c * x)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
      · intro h
        have e : (avg j B K fun y => |u y|)
            = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, |u (rep j B K c * x)| :=
          funext fun x => havg _ x
        rw [e]
        exact (integrable_finsetSum _ fun c _ => (h c).abs).const_mul _
    refine ⟨hI.trans (hIc.trans hAbs.symm), fun hint => ?_⟩
    have hcs := hIc.1 (hI.1 hint)
    have havgInt : IntegrableOn (avg j B K u) D μ := by
      have e : avg j B K u = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, u (rep j B K c * x) :=
        funext fun x => havg _ x
      rw [e]
      exact (integrable_finsetSum _ fun c _ => hcs c).const_mul _
    refine ⟨havgInt, ?_⟩
    have hint0 : IntegrableOn u (⋃ c, rep j B K c • D) μ := by
      rw [← hD0def]
      exact hI.1 hint
    rw [hD'.setIntegral_eq hD0 hinvΔ, hD0def, integral_iUnion_ae hmeasc hdisj hint0, tsum_fintype]
    have hterm : ∀ c, ∫ x in rep j B K c • D, u x ∂μ = ∫ x in D, u (rep j B K c * x) ∂μ :=
      fun c => (hmp _).setIntegral_image_emb (hemb _) u D
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← integral_finsetSum _ fun c _ => hcs c,
      ← integral_const_mul]
    congr 1
    ext x
    rw [havg, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

end PositivityTheory.KB.SpectralGap.UnfoldB

end
end
