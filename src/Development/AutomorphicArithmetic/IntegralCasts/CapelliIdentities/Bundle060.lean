module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

theorem UpperTheory.Reformulated.B.CMConjNegOfSqEqNegPos.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d hd x hx
  let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  have h : (φ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : (φ x).re * (φ x).im = 0 := by linarith
  have hr : (φ x).re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg (φ x).re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
end

section

theorem UpperTheory.Reformulated.B.ConjugateSqrtNeg.conj_sqrt_neg :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (d : ℕ) (x : E),
    (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : (NumberField.IsCMField.complexConj E x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exfalso
    have h1 := NumberField.IsCMField.complexEmbedding_complexConj E φ x
    rw [h] at h1
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h1.symm
    have h2 : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
    rw [hr] at h2
    have h3 : r ^ 2 = -(d : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h
end

section

theorem UpperTheory.Reformulated.B.Qh55.mem_real_of_sq :
    ∀ {Y : Type} [inst : Field Y] {δ : Y}
    {q : ℕ}, (0 : ℕ) < q → δ ^ (2 : ℕ) = (↑q : Y) → δ ∈ NumberField.maximalRealSubfield Y := by
  intro Y _ δ q hq h
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  have h1 : (φ δ) ^ 2 = (q : ℂ) := by rw [← map_pow, h, map_natCast]
  have h2 : (φ δ) ^ 2 = ((Real.sqrt q : ℝ) : ℂ) ^ 2 := by
    rw [h1, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
  · rw [h3, Complex.star_def, Complex.conj_ofReal]
  · rw [h3, star_neg, Complex.star_def, Complex.conj_ofReal]
end

section

open scoped Classical

theorem UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place :
    ∀ (F : Type) [inst : Field F]
    [inst_1 : NumberField F] [NumberField.IsTotallyComplex F] (x : F) (v : NumberField.InfinitePlace F),
    ∑ φ : F →+* ℂ with NumberField.InfinitePlace.mk φ = v, (φ : F → ℂ) x =
      (↑((2 : ℝ) * ((v.embedding : F → ℂ) x).re) : ℂ) := by
  intro F _ _ _ x v
  have hc : v.IsComplex := NumberField.IsTotallyComplex.isComplex v
  have hne : v.embedding ≠ NumberField.ComplexEmbedding.conjugate v.embedding := by
    intro h
    exact (NumberField.InfinitePlace.isComplex_iff.mp hc)
      (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm)
  have hset : (Finset.univ.filter fun φ : F →+* ℂ => NumberField.InfinitePlace.mk φ = v) =
      {v.embedding, NumberField.ComplexEmbedding.conjugate v.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h' : NumberField.InfinitePlace.mk v.embedding = NumberField.InfinitePlace.mk φ := by
        rw [NumberField.InfinitePlace.mk_embedding, h]
      rcases NumberField.InfinitePlace.mk_eq_iff.mp h' with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    · rintro (h | h)
      · rw [h, NumberField.InfinitePlace.mk_embedding]
      · rw [h, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  rw [hset, Finset.sum_pair hne, NumberField.ComplexEmbedding.conjugate_coe_eq,
    Complex.add_conj]
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe14.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

private lemma UpperTheory.Reformulated.B.Qe14.pow_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖η ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : η ^ (n + 1) - 1 = (η ^ n - 1) * (η - 1) + ((η ^ n - 1) + (η - 1)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ih h.le
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih h)

private lemma UpperTheory.Reformulated.B.Qe14.sum_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖∑ i ∈ Finset.range n, η ^ i - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∑ i ∈ Finset.range (n + 1), η ^ i - ((n + 1 : ℕ) : K)
        = (∑ i ∈ Finset.range n, η ^ i - (n : K)) + (η ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt ih (UpperTheory.Reformulated.B.Qe14.pow_close h n))

theorem UpperTheory.Reformulated.B.Qe14.root_eq_one :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {m : ℕ},
      ¬v ∣ m →
        ∀ {η : UpperTheory.Reformulated.B.Qe14.Om v},
          η ^ m = (1 : UpperTheory.Reformulated.B.Qe14.Om v) →
            ‖η - (1 : UpperTheory.Reformulated.B.Qe14.Om v)‖ < (1 : ℝ) → η = (1 : UpperTheory.Reformulated.B.Qe14.Om v) := by
  intro v inst m hm η hη h
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, η ^ i) * (η - 1) = 0 := by
    rw [geom_sum_mul, hη, sub_self]
  have h2 : ∑ i ∈ Finset.range m, η ^ i = 0 :=
    (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)
  have h3 := UpperTheory.Reformulated.B.Qe14.sum_close h m
  rw [h2, zero_sub, norm_neg] at h3
  have h4 : ((m : ℕ) : PadicAlgCl v) = algebraMap ℚ_[v] (PadicAlgCl v) (m : ℚ_[v]) := by
    simp
  have h5 : ‖((m : ℕ) : PadicAlgCl v)‖ = ‖(m : ℚ_[v])‖ := by
    rw [h4]; exact PadicAlgCl.norm_extends v _
  rw [h5, Padic.norm_natCast_lt_one_iff] at h3
  exact hm h3
end

section

namespace UpperTheory.Reformulated.B.S7

theorem eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 := by
  by_contra hne
  have hu1 : ‖u‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (u - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le h.le le_rfl)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : u ^ (i + 1) - 1 = (u ^ i - 1) * u + (u - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans_lt ih
  have hsum : ∀ n : ℕ, ‖(∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : PadicAlgCl l)
          = ((∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)) + (u ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hpow n))
  have h0 : (∑ i ∈ Finset.range m, u ^ i) = 0 := by
    have := geom_sum_mul u m
    rw [hu, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt := hsum m
  rw [h0, zero_sub, norm_neg] at hlt
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap'] at hlt
  exact hm (Padic.norm_natCast_lt_one_iff.mp hlt)

end UpperTheory.Reformulated.B.S7
end

section

theorem UpperTheory.Reformulated.B.QuotientBasisFiniteDimensional.qb_fd :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {ι : Type} [Finite ι]
    (f : ι → PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] ↥K ∧ ∀ (i : ι), f i ∈ K := by
  intro l _ ι _ f
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range f), ?_, fun i =>
    IntermediateField.subset_adjoin ℚ_[l] (Set.range f) ⟨i, rfl⟩⟩
  haveI : Finite (Set.range f) := (Set.finite_range f).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    Algebra.IsIntegral.isIntegral x
end

section

noncomputable def UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rwa [norm_neg] }
end

section

noncomputable def UpperTheory.Reformulated.B.CapelliIdentity₂.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha }
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza4.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.Yza4.Cg :
    {l : ℕ} → [inst : Fact (Nat.Prime l)] → ℕ → UpperTheory.Reformulated.B.Yza4.Qbar l → UpperTheory.Reformulated.B.Yza4.Qbar l → Prop :=
    fun {l : ℕ} [Fact (Nat.Prime l)] (n : ℕ) (a b : UpperTheory.Reformulated.B.Yza4.Qbar l) ↦
      ‖a - b‖ ≤ ‖(↑l : UpperTheory.Reformulated.B.Yza4.Qbar l) ^ n‖

theorem UpperTheory.Reformulated.B.Yza4.congruence_mul_of_unit_factor :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {n : ℕ} {P h un D : UpperTheory.Reformulated.B.Yza4.Qbar l},
      UpperTheory.Reformulated.B.Yza4.Cg n (P * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) →
        UpperTheory.Reformulated.B.Yza4.Cg n P (un * D) →
          ‖un‖ = (1 : ℝ) → ‖h‖ ≤ (1 : ℝ) → UpperTheory.Reformulated.B.Yza4.Cg n (D * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) := by
  intro l _ n P h un D h1 h2 hu hh
  unfold UpperTheory.Reformulated.B.Yza4.Cg at *
  rw [sub_zero] at h1 ⊢
  set c : ℝ := ‖(↑l : PadicAlgCl l) ^ n‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hmul : ∀ a b : PadicAlgCl l, ‖a * b‖ = ‖a‖ * ‖b‖ := fun a b => norm_mul a b
  have key : un * (D * h) = P * h + (un * D - P) * h := by ring
  have h3 : ‖(un * D - P) * h‖ ≤ c := by
    rw [hmul, norm_sub_rev]
    calc ‖P - un * D‖ * ‖h‖ ≤ c * 1 := mul_le_mul h2 hh (norm_nonneg _) hc0
      _ = c := mul_one c
  have h4 : ‖un * (D * h)‖ ≤ c := by
    rw [key]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le h1 h3)
  rw [hmul, hu, one_mul] at h4
  exact h4
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk7.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qk7.iof_add :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {x y : UpperTheory.Reformulated.B.Qk7.Om v}, ‖x‖ < (1 : ℝ) → ‖y‖ < (1 : ℝ) → ‖x + y‖ < (1 : ℝ) := by
  intro v inst x y hx hy
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
end

section

theorem UpperTheory.Reformulated.B.Qj1.mem_of_adjoin_top.{u_2} :
    ∀ {l : ℕ}
    [inst : Fact (Nat.Prime l)] {K : Type u_2} [inst_1 : Field K] [inst_2 : CharZero K] {S : Set K},
    Algebra.adjoin ℚ S = ⊤ →
      ∀ (j : K →+* PadicAlgCl l) (F : IntermediateField ℚ_[l] (PadicAlgCl l)),
        (∀ s ∈ S, (j : K → PadicAlgCl l) s ∈ F) → ∀ (x : K), (j : K → PadicAlgCl l) x ∈ F := by
  intro l _ K _ _ S hS j F hF x
  have hx : x ∈ Algebra.adjoin ℚ S := hS ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact hF y hy
  | algebraMap q =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem F q
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact add_mem hy hz
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact mul_mem hy hz
end
