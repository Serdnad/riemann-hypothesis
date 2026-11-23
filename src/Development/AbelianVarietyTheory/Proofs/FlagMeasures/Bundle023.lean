module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle013
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle016
public import ReciprocityTheory.Automorphisms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SumIntegralComparisons
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

section

open MeasureTheory NumberField Finset
open scoped ArithmeticFunction.zeta

namespace GlobalTheory.IdealZetaSum

theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) ≤ s / (s - 1) := by
  have hs1 : 0 < s - 1 := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Ioc_self, sum_empty]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have : (1 : ℝ) ≤ x := by simpa using hx.1
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have h := AntitoneOn.sum_le_integral_Ico hN hanti
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by simpa using hN1)]; simp⟩)] at h
  have e : ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)
      = 1 + ∑ i ∈ Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    rw [sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) 1 N 1]
    have : Ioc 0 N = insert 1 (Ico (1 + 1) (N + 1)) := by
      ext n; simp only [mem_Ioc, mem_insert, mem_Ico]; omega
    rw [this, sum_insert (by simp)]
    simp
  rw [e]
  have hpos : 0 ≤ (N : ℝ) ^ (-s + 1) := by positivity
  have h2 : ((N : ℝ) ^ (-s + 1) - ((1 : ℕ) : ℝ) ^ (-s + 1)) / (-s + 1) ≤ 1 / (s - 1) := by
    rw [Nat.cast_one, Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div]
    rw [show -s + 1 = -(s - 1) by ring] at hpos
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  have h3 : s / (s - 1) = 1 + 1 / (s - 1) := by field_simp; ring
  linarith

theorem sum_zeta_pow_mul_rpow_le (s : ℝ) (N k : ℕ) :
    ∑ n ∈ Ioc 0 N, (((ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
      ≤ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul, sum_ite_eq']
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s))]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (sum_nonneg fun n _ => by positivity))
    rw [sum_mul_sum, ← sum_product', pow_succ]
    have e : ∀ n ∈ Ioc 0 N, (((ζ ^ k * ζ : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
        = ∑ x ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          (((ζ ^ k : ArithmeticFunction ℕ) x.1 : ℕ) : ℝ) * (x.1 : ℝ) ^ (-s) * (x.2 : ℝ) ^ (-s) := by
      intro n hn
      rw [mem_Ioc] at hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_mul]
      refine sum_congr ?_ ?_
      · ext x
        simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Ioc]
        constructor
        · rintro ⟨h, h0⟩
          have h1 : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          have h2 : 0 < x.2 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h⟩ <;> nlinarith
        · rintro ⟨_, h⟩
          exact ⟨h, by omega⟩
      · intro x hx
        simp only [mem_filter, mem_product, mem_Ioc] at hx
        rw [← hx.2, Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
          ArithmeticFunction.zeta_apply_ne hx.1.2.1.ne']
        simp [mul_assoc]
    rw [sum_congr rfl e, sum_fiberwise_eq_sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => by positivity

theorem sum_absNorm_rpow_neg_le : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s →
    ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) →
      ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ s hs S hS
  classical
  set N := S.sup (fun I => Ideal.absNorm I) with hN
  refine le_trans ?_ (pow_le_pow_left₀ (sum_nonneg fun n _ => by positivity)
    (sum_Ioc_rpow_neg_le hs N) _)
  refine le_trans ?_ (sum_zeta_pow_mul_rpow_le s N _)
  rw [← sum_fiberwise_of_maps_to (s := S) (t := Ioc 0 N) (g := fun I => Ideal.absNorm I)]
  · refine sum_le_sum fun n hn => ?_
    rw [sum_congr rfl (g := fun _ => (n : ℝ) ^ (-s))
      (fun I hI => by rw [(mem_filter.mp hI).2]), sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Nat.cast_le]
    refine le_trans ?_ (ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun I hI => (mem_filter.mp (mem_coe.mp hI)).2)
      (Ideal.finite_setOfPred_absNorm_eq n)
  · intro I hI
    rw [mem_Ioc]
    exact ⟨Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hS I hI),
      le_sup (f := fun I => Ideal.absNorm I) hI⟩

end GlobalTheory.IdealZetaSum
end

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem card_hermitian_dvd_sq {A : Type} [CommRing A] [Finite A] (c : A →+* A)
    (hc : ∀ u, c (c u) = u) (ω : A) (hω : IsUnit (ω - c ω)) (p : A) (hp : c p = p) (m : ℕ) :
    Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2
      = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  have hmem : ∀ u : A, u ∈ Ideal.span {p} → c u ∈ Ideal.span {p} := by
    intro u hu
    rw [Ideal.mem_span_singleton] at hu ⊢
    have := map_dvd c hu
    rwa [hp] at this
  let σ : (Fin m → Fin m → Ideal.span {p}) →+ (Fin m → Fin m → Ideal.span {p}) :=
    { toFun := fun H a b => ⟨c (H b a).1, hmem _ (H b a).2⟩
      map_zero' := by
        funext a b
        exact Subtype.ext (by simp)
      map_add' := fun H K => by
        funext a b
        exact Subtype.ext (by simp) }
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    funext a b
    exact Subtype.ext (hc _)
  have hs : ∀ (r : A) x, σ (r • x) = c r • σ x := fun r x => by
    funext a b
    exact Subtype.ext (map_mul c r _)
  have h := (card_fixed_sq c hc hω σ hσ hs).1
  let e : {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ≃
      {x : Fin m → Fin m → Ideal.span {p} // σ x = x} :=
    { toFun := fun H => ⟨fun a b => ⟨H.1 a b, Ideal.mem_span_singleton.2 (H.2.2 a b)⟩, by
        funext a b
        exact Subtype.ext (H.2.1 a b)⟩
      invFun := fun x => ⟨fun a b => (x.1 a b).1,
        fun a b => congrArg Subtype.val (congrFun (congrFun x.2 a) b),
        fun a b => Ideal.mem_span_singleton.1 (x.1 a b).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : {u : A // p ∣ u} ≃ Ideal.span {p} :=
    Equiv.subtypeEquivRight fun u => Ideal.mem_span_singleton.symm
  rw [Nat.card_congr e, h, Nat.card_congr e2, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp

end GlobalTheory.GramCount
end

section

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc

noncomputable def idemPairHom {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) : F × F →ₐ[F] E :=
  AlgHom.ofLinearMap
    ((LinearMap.toSpanSingleton F E p).coprod (LinearMap.toSpanSingleton F E q))
    (by simpa using h1)
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp only [Prod.mk_mul_mk, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, map_mul]
      linear_combination
        (-(algebraMap F E a * algebraMap F E c * p) - algebraMap F E b * algebraMap F E d * q) * h1
        + (algebraMap F E a * algebraMap F E c + algebraMap F E b * algebraMap F E d
          - algebraMap F E a * algebraMap F E d - algebraMap F E b * algebraMap F E c) * h0)

end GlobalTheory.SgLoc
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.exists_measurable_coset_section' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G), IsClosed (L : Set G) → ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  first | exact @GlobalTheory.exists_measurable_coset_section | exact GlobalTheory.exists_measurable_coset_section | (intros; apply GlobalTheory.exists_measurable_coset_section <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d → (∀ x, 0 ≤ d x) → (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b → Integrable (fun x => Real.exp (-(b * d x))) μ := by
  first | exact @GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | (intros; apply GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth <;> assumption)
end

section

open MeasureTheory

namespace GlobalTheory.StabUnfold


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.StabUnfold.exists_cutoff_doubleCoset : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (K : Subgroup G) (K' : Subgroup H) (x : G) (S : Set G), IsOpen (K : Set G) → IsOpen (K' : Set H) → IsCompact (K' : Set H) → (∀ h, h ∈ K' ↔ x⁻¹ * j h * x ∈ K) → (∀ g, g ∈ S ↔ ∃ h, ∃ k ∈ K, g = j h * x * k) → ∃ b : G → ENNReal, Measurable b ∧ (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) ∧ ∫⁻ g, S.indicator 1 g * b g ∂μ = μ K / ν K' := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ j hj K K' x S hK hK'o hK'c hK'K hS
  obtain ⟨b₀, hb₀m, hb₀⟩ := _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one G H ν j hj
  have hSeq : S = ⋃ h : H, (fun g => j h * x * g) '' (K : Set G) := by
    ext g
    rw [hS g]
    simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor <;> rintro ⟨h, k, hk, e⟩ <;> exact ⟨h, k, hk, e.symm⟩
  have hSopen : IsOpen S := by
    rw [hSeq]
    exact isOpen_iUnion fun h => isOpenMap_mul_left (j h * x) _ hK
  have hSm : MeasurableSet S := hSopen.measurableSet
  set T : Set G := (fun g => x⁻¹ * g) ⁻¹' (K : Set G) with hT_def
  have hTm : MeasurableSet T := measurable_const_mul x⁻¹ hK.measurableSet
  have hc0 : ν K' ≠ 0 := (hK'o.measure_pos ν ⟨1, K'.one_mem⟩).ne'
  have hcT : ν K' ≠ ∞ := hK'c.measure_lt_top.ne
  have hSinv : ∀ h g, j h * g ∈ S ↔ g ∈ S := by
    intro h g
    rw [hS, hS]
    constructor
    · rintro ⟨h', k, hk, e⟩
      refine ⟨h⁻¹ * h', k, hk, ?_⟩
      have e' : g = (j h)⁻¹ * (j h' * x * k) := by rw [← e]; group
      rw [e', map_mul, map_inv]; group
    · rintro ⟨h', k, hk, e⟩
      exact ⟨h * h', k, hk, by rw [e, map_mul]; group⟩
  have hTS : ∀ g, g ∈ T → g ∈ S := by
    intro g hg
    rw [hS]
    exact ⟨1, x⁻¹ * g, hg, by simp⟩
  have hcoset : ∀ g ∈ S, ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 1 := by
    intro g hg
    obtain ⟨h0, k, hk, rfl⟩ := (hS g).1 hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k))
        = (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) := by
      intro h
      have hiff : j h * (j h0 * x * k) ∈ T ↔ h * h0 ∈ (K' : Set H) := by
        show x⁻¹ * (j h * (j h0 * x * k)) ∈ K ↔ h * h0 ∈ K'
        rw [hK'K, map_mul]
        have e2 : x⁻¹ * (j h * (j h0 * x * k)) = x⁻¹ * (j h * j h0) * x * k := by group
        rw [e2, Subgroup.mul_mem_cancel_right _ hk]
      by_cases hm : h * h0 ∈ (K' : Set H)
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (mt hiff.1 hm)]
    calc ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k)) ∂ν
        = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) ∂ν := lintegral_congr e
      _ = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) h ∂ν :=
          lintegral_mul_right_eq_self (fun h => (K' : Set H).indicator (fun _ => (ν K')⁻¹) h) h0
      _ = 1 := by rw [lintegral_indicator_const hK'o.measurableSet, ENNReal.inv_mul_cancel hc0 hcT]
  have hzero : ∀ g, g ∉ S → ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 0 := by
    intro g hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) = 0 := fun h =>
      Set.indicator_of_notMem (fun hT => hg ((hSinv h g).1 (hTS _ hT))) _
    simp [e]
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  refine ⟨fun g => T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g,
    (measurable_const.indicator hTm).add (hb₀m.indicator hSm.compl), fun g => ?_, ?_⟩
  · dsimp only
    rw [lintegral_add_left (show Measurable fun h => T.indicator (fun _ => (ν K')⁻¹) (j h * g)
      from (measurable_const.indicator hTm).comp (hjg g))]
    by_cases hg : g ∈ S
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = 0 := fun h =>
        Set.indicator_of_notMem (show j h * g ∉ Sᶜ from fun hc => hc ((hSinv h g).2 hg)) _
      simp only [e, lintegral_zero, add_zero]
      exact hcoset g hg
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = b₀ (j h * g) := fun h =>
        Set.indicator_of_mem (show j h * g ∈ Sᶜ from fun hs => hg ((hSinv h g).1 hs)) _
      rw [hzero g hg, zero_add]
      simp only [e]
      exact hb₀ g
  · have e : ∀ g, S.indicator 1 g * (T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g)
        = T.indicator (fun _ => (ν K')⁻¹) g := by
      intro g
      by_cases hg : g ∈ S
      · simp [hg]
      · have hgT : g ∉ T := fun hT => hg (hTS g hT)
        simp [hg, hgT]
    rw [lintegral_congr e, lintegral_indicator_const hTm, hT_def, measure_preimage_mul,
      ENNReal.div_eq_inv_mul]

end GlobalTheory.StabUnfold
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.exists_measurable_lintegral_coset_eq_one_closedSubgroup : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  first | exact @GlobalTheory.exists_measurable_lintegral_coset_eq_one | exact GlobalTheory.exists_measurable_lintegral_coset_eq_one | (intros; apply GlobalTheory.exists_measurable_lintegral_coset_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' : ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  first | exact @GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | exact GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | (intros; apply GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  first | exact @GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | exact GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | (intros; apply GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq <;> assumption)
end

section

open NumberField

namespace GlobalTheory

theorem classNumber_le_minkowski_count :
    ∀ (K : Type) [Field K] [NumberField K], (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (1 + Real.log (Real.sqrt |(discr K : ℝ)|)) ^ Module.finrank ℚ K :=
  fun K _ _ => classNumber_le_sqrt_discr_mul_pow K

end GlobalTheory
end

section

open scoped Classical

theorem _root_.GlobalTheory.T.sum_prod_of_local_choices_bijection : ∀ {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)] (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p)), (∀ p ∈ s, (U p).Finite) → (∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c') → (∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p) → (∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p) → ∀ g : ∀ p, O p → R, Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0) = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  first | exact @GlobalTheory.prod_sum_of_local_choices | exact GlobalTheory.prod_sum_of_local_choices | (intros; apply GlobalTheory.prod_sum_of_local_choices <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory


open Classical in
theorem equivFinsuppOfBasisLeft_lTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] [DecidableEq ι]
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : M ⊗[K] N) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem AL_eq_zero_of_compAt (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L)
    (h : ∀ v, ReciprocityTheory.Aut.compAt L v a = 0) : a = 0 := by
  classical
  set K := maximalRealSubfield L
  let b := Module.finBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := AFplus L) b
  have hc : ∀ i, e a i = 0 := by
    intro i
    refine RestrictedProduct.ext _ _ (fun v => ?_)
    have h1 : ∀ x, ReciprocityTheory.Aut.compAt L v x =
        LinearMap.lTensor L (ReciprocityTheory.Aut.evalAt L v).toLinearMap x := by
      intro x
      simp only [ReciprocityTheory.Aut.compAt]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add (f := _)] at *; rw [hx, hy]
    have h2 := equivFinsuppOfBasisLeft_lTensor b (ReciprocityTheory.Aut.evalAt L v).toLinearMap a i
    rw [← h1 a, h v, map_zero, Finsupp.zero_apply] at h2
    exact h2.symm
  have : e a = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

end GlobalTheory
end
