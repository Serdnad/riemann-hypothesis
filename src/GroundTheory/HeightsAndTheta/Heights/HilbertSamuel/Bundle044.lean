module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def RealGramComparison.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ), IsProjFrame d.x e →
    (fun n => resChi d n - resCChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)), IsProjFrame d.x e → IsSmoothMetric m →
    mInt d.R.A (fun _ => resPot d m) (fun _ => 1) = (projDeg d.x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace QuotPartGraded

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def blockWeight (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun x => Pi.single x.1 1

theorem blockWeight_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = ∑ i, (d ⟨k, i⟩ : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • blockWeight ι i) (by intro i; simp),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (p : MRingOver S ι) (a : K → ℕ) :
    IsMultiHomog p a ↔ IsWeightedHomogeneous (blockWeight ι) p (fun k => (a k : ℤ)) := by
  unfold IsMultiHomog
  constructor
  · intro h d hd
    funext k
    rw [blockWeight_apply]
    have := h d (mem_support_iff.2 hd) k
    exact_mod_cast this
  · intro h m hm k
    have := congrFun (h (mem_support_iff.1 hm)) k
    rw [blockWeight_apply] at this
    exact_mod_cast this

theorem nonneg_of_isWeightedHomogeneous {p : MRingOver S ι} {c : K → ℤ}
    (hp : IsWeightedHomogeneous (blockWeight ι) p c) (h0 : p ≠ 0) : ∀ k, 0 ≤ c k := by
  obtain ⟨d, hd⟩ := ne_zero_iff.1 h0
  intro k
  rw [← hp hd, blockWeight_apply]
  positivity

theorem span_eq (c : K → ℤ) :
    Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)} =
      weightedHomogeneousSubmodule S (blockWeight ι) c := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro p ⟨hc, hp⟩
    rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
    have h' := (isMultiHomog_iff p _).1 hp
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h'
  · intro p hp
    by_cases h0 : p = 0
    · rw [h0]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      have hc := nonneg_of_isWeightedHomogeneous hp h0
      refine ⟨hc, (isMultiHomog_iff p _).2 ?_⟩
      have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
      rw [hcc]
      exact hp

theorem quotPart_eq (V : Ideal (MRingOver S ι)) (c : K → ℤ) :
    KH.quotPart S V c =
      (weightedHomogeneousSubmodule S (blockWeight ι) c).map (Ideal.Quotient.mkₐ S V).toLinearMap := by
  rw [KH.quotPart, ← span_eq, Submodule.map_span]
  rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous {V : Ideal (MRingOver S ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨fun k => (a k : ℤ), (isMultiHomog_iff f a).1 ha⟩

end QuotPartGraded

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem QuotPartGraded.proof : QuotPartGraded.Statement := by
  intro S _ K _ ι _ V hV
  have hq := QuotPartGraded.quotPart_eq (S := S) (ι := ι) V
  refine ⟨?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum
      have hlift : ∀ c, ∃ p : MRingOver S ι, c ∈ s →
          (p ∈ weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c ∧
            Ideal.Quotient.mk V p = v c) := by
        intro c
        by_cases hc : c ∈ s
        · have h1 := hv c hc
          rw [hq] at h1
          obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 h1
          exact ⟨y, fun _ => ⟨hy, hyv⟩⟩
        · exact ⟨0, fun h => absurd h hc⟩
      choose p hp using hlift
      have hsumV : ∑ c ∈ s, p c ∈ V := by

        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hsum]
        exact Finset.sum_congr rfl fun c hc => (hp c hc).2
      intro c hc
      have hcomp := weightedHomogeneousComponent_mem_of_mem S (QuotPartGraded.blockWeight ι)
        (QuotPartGraded.isHomogeneous hV) hsumV c

      rw [map_sum, Finset.sum_eq_single c] at hcomp
      · rw [← (hp c hc).2, Ideal.Quotient.eq_zero_iff_mem]
        rwa [weightedHomogeneousComponent_eq_self (hp c hc).1] at hcomp
      · intro d hd hdc
        exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne c (hp d hd).1 (Ne.symm hdc)
      · intro h
        exact absurd hc h
    · have htop := (DirectSum.Decomposition.isInternal
        (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι))).submodule_iSup_eq_top
      rw [show KH.quotPart S V = fun c => (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c).map
          (Ideal.Quotient.mkₐ S V).toLinearMap from funext hq]
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective S V
  · intro a c p m hp hm
    rw [hq] at hm ⊢
    obtain ⟨q, hq', rfl⟩ := Submodule.mem_map.1 hm
    refine Submodule.mem_map.2 ⟨p * q, ?_, ?_⟩
    · have := ((QuotPartGraded.isMultiHomog_iff p a).1 hp).mul hq'
      rw [mem_weightedHomogeneousSubmodule, add_comm]
      exact this
    · simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

namespace ArithmeticVolumeBigDimensionOne

theorem le_limsup_div {u : ℕ → ℝ} {T C C' : ℝ}
    (hlo : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * T - C ≤ u n) (hup : ∀ n : ℕ, u n ≤ C' * ((n : ℝ) + 1)) :
    T ≤ limsup (fun n : ℕ => u n / n) atTop := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => u n / n) := by
    refine isBoundedUnder_of_eventually_le (a := 2 * |C'|) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by linarith)]
    calc u n ≤ C' * ((n : ℝ) + 1) := hup n
      _ ≤ |C'| * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ 2 * |C'| * n := by nlinarith [abs_nonneg C']
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have key : T - ε ≤ limsup (fun n : ℕ => u n / n) atTop := by
    refine le_limsup_of_frequently_le (Eventually.frequently ?_) hb
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    rw [le_div_iff₀ (by linarith)]
    have hC : C < n * ε := (div_lt_iff₀ hε).mp (hN.trans_le hnN)
    have hl := hlo n hn1
    nlinarith
  linarith

end ArithmeticVolumeBigDimensionOne

theorem ArithmeticVolumeBigDimensionOne.proof (hP : PackingStatement) (hL : CurveSmallCountLower.Statement) :
    ArithmeticVolumeBigDimensionOne.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII har hb hP0 hs hnef hc
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII har hb hs.1 hc
  obtain ⟨-, C', hC'⟩ := hP K ι Ω y 0 A (chartLat y A.a) har hb hs.1
    (fun τ => SmallSectionPointHeight.chartLat_le_chartLatNm y A.a τ)
  have e : arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0 =
      limsup (fun n : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n / n) atTop := by
    unfold arVolP
    congr 1
    simp
  rw [e]
  exact ArithmeticVolumeBigDimensionOne.le_limsup_div hC (fun n => by simpa using hC' n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepLocal

def powMulSub {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω) (v : Ω) (hv : v ∈ R) : Subalgebra ℤ Ω where
  carrier := {x | ∃ E : ℕ, x * v ^ E ∈ R}
  mul_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : x * z * v ^ (E₁ + E₂) = (x * v ^ E₁) * (z * v ^ E₂) := by ring
    rw [e]; exact R.mul_mem h₁ h₂
  add_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : (x + z) * v ^ (E₁ + E₂) = (x * v ^ E₁) * v ^ E₂ + (z * v ^ E₂) * v ^ E₁ := by ring
    rw [e]; exact R.add_mem (R.mul_mem h₁ (R.pow_mem hv _)) (R.mul_mem h₂ (R.pow_mem hv _))
  algebraMap_mem' r := ⟨0, by rw [pow_zero, mul_one]; exact R.algebraMap_mem r⟩

theorem pow_twist {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (c : ∀ k, ι k) (g w : Ω) (n : ℕ) :
    g * w ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) = g * (w * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ n := by
  rw [mul_pow, ← Finset.prod_pow, mul_assoc]
  congr 3; funext k
  rw [← zpow_natCast, ← zpow_mul]; ring_nf

end SpanStepLocal


open SpanStepLocal in
theorem SpanStepLocal.proof (hR : RelLatticeFinite.Statement) : SpanStepLocal.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen j hj
  classical
  set P := Algebra.adjoin ℤ (Set.range fun i => w i / w j) with hPdef

  set v : (∀ k, ι k) → Fin q → Ω := fun c i => w i * ∏ k, y ⟨k, c k⟩ ^ (-a k) with hvdef
  have hv : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ i, v c i ∈ chartRingZ y c := fun c hc i => by
    simpa [hvdef] using hw i c hc
  have hv0 : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → v c j ≠ 0 := fun c hc =>
    mul_ne_zero hj (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
  have hquot : ∀ c i, w i / w j * v c j = v c i := fun c i => by
    simp only [hvdef]; rw [← mul_assoc, div_mul_cancel₀ _ hj]
  have hrel : ∀ (g : Ω) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (g ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ↔
      g * ∏ k, y ⟨k, c k⟩ ^ (-(((0 : ℕ) : ℤ) * (fun _ => (0 : ℤ)) k)) ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) := fun g c _ => by simp

  have incl₁ : ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n → g ∈ relChartLat P y (fun _ => 0) 0 := by
    intro g n hg c hc
    rw [← hrel g c hc]
    set S := Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
    have hRS : ∀ x ∈ chartRingZ y c, x ∈ S := fun x hx =>
      (Algebra.adjoin_le Algebra.subset_adjoin : chartRingZ y c ≤ S.restrictScalars ℤ) hx
    have hPS : ∀ x ∈ P, x ∈ S := fun x hx => S.algebraMap_mem (⟨x, hx⟩ : P)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hinv : (∑ i, u i * (w i / w j)) = (v c j)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [Finset.sum_mul, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, hquot]
    have hinvS : (v c j)⁻¹ ∈ S := hinv ▸ S.sum_mem fun i _ =>
      S.mul_mem (hRS _ (hu i)) (hPS _ (Algebra.subset_adjoin ⟨i, rfl⟩))
    have hgv : g * v c j ^ n ∈ S := hRS _ (by rw [← pow_twist]; exact hg c hc)
    have e : g = g * v c j ^ n * (v c j)⁻¹ ^ n := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (hv0 c hc), one_pow, mul_one]
    rw [e]; exact S.mul_mem hgv (S.pow_mem hinvS n)
  have incl₂ : ∀ g ∈ relChartLat P y (fun _ => 0) 0, ∃ n : ℕ, g * w j ^ n ∈ chartLat y a n := by
    intro g hg
    have hE : ∀ c, ∃ E : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → g * v c j ^ E ∈ chartRingZ y c := by
      intro c
      by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
      swap; · exact ⟨0, fun h => absurd h hc⟩
      have hgS := (hrel g c hc).2 (hg c hc)
      have hg' : g ∈ Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
        rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact hgS
      have hle : Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ≤ powMulSub _ _ (hv c hc j) := by
        refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
        · rintro _ ⟨i, rfl⟩; exact ⟨1, by rw [pow_one, hquot]; exact hv c hc i⟩
        · rintro _ ⟨p, rfl⟩; exact ⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨p, rfl⟩⟩
      obtain ⟨E, hE⟩ := hle hg'
      exact ⟨E, fun _ => hE⟩
    choose E hE using hE
    refine ⟨∑ c, E c, fun c hc => ?_⟩
    rw [pow_twist]
    have e : g * v c j ^ (∑ c, E c) = g * v c j ^ E c * v c j ^ (∑ c, E c - E c) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c))]
    rw [e]; exact (chartRingZ y c).mul_mem (hE c hc) ((chartRingZ y c).pow_mem (hv c hc j) _)

  obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (hR K ι Ω y (fun _ => 0) 0 q (fun i => w i / w j) hy)
  have hbmem : ∀ l, b l ∈ relChartLat P y (fun _ => 0) 0 := fun l =>
    hb ▸ Submodule.subset_span ⟨l, rfl⟩
  refine ⟨r, b, fun l => incl₂ _ (hbmem l), fun g n hg => ?_⟩
  have hgN := incl₁ g n hg
  rw [← hb, Submodule.mem_span_range_iff_exists_fun] at hgN
  obtain ⟨c, hc⟩ := hgN
  exact ⟨fun l => (c l : Ω), fun l => (c l).2, by rw [← hc]; rfl⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

set_option linter.unusedSectionVars false

namespace LiftBirationalNef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem exists_int_of_rat (f : MRingOver ℚ ι) :
    ∃ (m : ℕ) (F : MRing ι), 0 < m ∧ MvPolynomial.map (Int.castRingHom ℚ) F = C (m : ℚ) * f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, monomial u a.num, a.den_pos, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    rw [eq_intCast, mul_comm, Rat.mul_den_eq_num]
  | add p q hp hq =>
    obtain ⟨m1, F1, hm1, h1⟩ := hp
    obtain ⟨m2, F2, hm2, h2⟩ := hq
    refine ⟨m1 * m2, C (m2 : ℤ) * F1 + C (m1 : ℤ) * F2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_C, map_C, h1, h2]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring

theorem mConeMapOver_map (y : (Σ k, ι k) → Ω) (F : MRing ι) :
    KH.mConeMapOver ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = mConeMap y F := by
  rw [← algebraMap_int_eq]
  exact MvPolynomial.aeval_map_algebraMap ℚ _ F

theorem genIdeal_eq (y : (Σ k, ι k) → Ω) : KH.genIdeal y = KH.mIdealOver ℚ y := by
  apply le_antisymm
  · rw [KH.genIdeal, Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, KH.mIdealOver, RingHom.mem_ker, mConeMapOver_map]
    exact hF
  · intro f hf
    obtain ⟨m, F, hm, hF⟩ := exists_int_of_rat f
    rw [KH.mIdealOver, RingHom.mem_ker] at hf
    have hF0 : F ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, ← mConeMapOver_map, hF, map_mul, hf, mul_zero]
    have hmap : MvPolynomial.map (Int.castRingHom ℚ) F ∈ KH.genIdeal y := Ideal.mem_map_of_mem _ hF0
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hf' : f = C ((m : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F := by
      rw [hF, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hf']
    exact Ideal.mul_mem_left _ _ hmap

theorem coord_ne_zero_of_not_mem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

theorem aeval_scale {y : (Σ k, ι k) → Ω} (lam : K → Ω) {G : MRing ι} {d : K → ℕ} (hG : IsMultiHomog G d) :
    aeval (fun p => lam p.1 * y p) G = (∏ k, lam k ^ d k) * aeval y G := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  have hl : ∏ p : Σ k, ι k, lam p.1 ^ m p = ∏ k, lam k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, lam k ^ m ⟨k, i⟩ = lam k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hG m hm k]
  rw [hl]
  ring

end LiftBirationalNef


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
