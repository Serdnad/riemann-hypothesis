module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open NNReal

section Integers

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

abbrev normInteger : Subring K := (NormedField.valuation (K := K)).integer

variable {K}

theorem mem_normInteger {x : K} : x ∈ normInteger K ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

theorem normInteger_integers : (NormedField.valuation (K := K)).Integers (normInteger K) :=
  Valuation.integer.integers _


theorem mem_span_singleton_pow_iff {a x : normInteger K} (n : ℕ) :
    x ∈ Ideal.span {a} ^ n ↔ ‖(x : K)‖ ≤ ‖(a : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    calc ‖(y : K)‖ * ‖(a : K)‖ ^ n ≤ 1 * ‖(a : K)‖ ^ n := by
          gcongr; exact mem_normInteger.1 y.2
      _ = _ := one_mul _
  · intro hx
    by_cases ha : (a : K) ^ n = 0
    · refine ⟨0, ?_⟩
      have : ‖(x : K)‖ = 0 := le_antisymm (by simpa [← norm_pow, ha] using hx) (norm_nonneg _)
      ext; simp [norm_eq_zero.1 this]
    · refine ⟨⟨(x : K) / (a : K) ^ n, mem_normInteger.2 ?_⟩, ?_⟩
      · rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ hx (by positivity)
      · ext; simp [div_mul_cancel₀ _ ha]

theorem isAdicComplete_span_singleton [CompleteSpace K] {a : normInteger K}
    (ha : ‖(a : K)‖ < 1) : IsAdicComplete (Ideal.span {a}) (normInteger K) := by
  have hmem : ∀ (n : ℕ) (x y : normInteger K),
      x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule (normInteger K) (normInteger K))] ↔
        ‖(x : K) - y‖ ≤ ‖(a : K)‖ ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_singleton_pow_iff]
    simp
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    simp only [hmem, ZeroMemClass.coe_zero, sub_zero] at hx
    have ht : Filter.Tendsto (fun n : ℕ => ‖(a : K)‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht hx
    ext; simpa using this
  · intro f hf
    simp only [hmem] at hf
    have ht : Filter.Tendsto (fun n : ℕ => ‖(a : K)‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
    have hc : CauchySeq (fun n => (f n : K)) := by
      refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact (hf hn).trans_lt (hN N le_rfl)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 :=
      le_of_tendsto' hL.norm fun n => mem_normInteger.1 (f n).2
    refine ⟨⟨L, mem_normInteger.2 hL1⟩, fun n => (hmem n _ _).2 ?_⟩
    have h2 : Filter.Tendsto (fun m => (f n : K) - f m) Filter.atTop (nhds ((f n : K) - L)) :=
      tendsto_const_nhds.sub hL
    exact le_of_tendsto h2.norm (Filter.eventually_atTop.2 ⟨n, fun m hm => hf hm⟩)

theorem surjective_pow_modP_of_exists_pow_eq {p : ℕ} (hp : p ≠ 0)
    (h : ∀ x : K, ‖x‖ ≤ 1 → ∃ y : K, y ^ p = x) :
    Function.Surjective (fun x : ModP (normInteger K) p => x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy⟩ := h x (mem_normInteger.1 x.2)
  have hy1 : ‖y‖ ≤ 1 := by
    have : ‖y‖ ^ p ≤ 1 := by rw [← norm_pow, hy]; exact mem_normInteger.1 x.2
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp).1 this
  refine ⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩
  simp only [← map_pow]
  congr 1
  ext; simp [hy]

end Integers

class IsPerfectoidField (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] : Prop where

  complete : CompleteSpace K

  norm_natCast_lt_one : ‖(p : K)‖ < 1

  exists_norm_mem_Ioo : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1

  surjective_pow : Function.Surjective (fun x : ModP (normInteger K) p => x ^ p)

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]

theorem completeSpace (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] : CompleteSpace K :=
  IsPerfectoidField.complete p

theorem norm_natCast_integer_lt_one : ‖((p : normInteger K) : K)‖ < 1 := by
  simpa using IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)

instance fact_not_isUnit : Fact (¬ IsUnit (p : normInteger K)) := by
  refine ⟨fun hu => ?_⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ‖((u : normInteger K) : K)‖ * ‖(((u⁻¹ : (normInteger K)ˣ) : normInteger K) : K)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  have ha : ‖((u : normInteger K) : K)‖ < 1 := hu ▸ norm_natCast_integer_lt_one p
  have hb := mem_normInteger.1 ((u⁻¹ : (normInteger K)ˣ) : normInteger K).2
  nlinarith [norm_nonneg ((u : normInteger K) : K)]

instance fact_valuation_ne_one : Fact (NormedField.valuation (p : K) ≠ 1) := by
  refine ⟨fun h => ?_⟩
  have h' : ‖(p : K)‖ = 1 := by
    rw [NormedField.valuation_apply] at h
    exact congrArg NNReal.toReal h
  exact (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)).ne h'

instance isAdicComplete : IsAdicComplete (Ideal.span {(p : normInteger K)}) (normInteger K) :=
  haveI := completeSpace (K := K) p
  isAdicComplete_span_singleton (norm_natCast_integer_lt_one p)

theorem surjective_frobenius : Function.Surjective (frobenius (ModP (normInteger K) p) p) :=
  IsPerfectoidField.surjective_pow

theorem surjective_fontaineTheta : Function.Surjective (WittVector.fontaineTheta (normInteger K) p) :=
  _root_.surjective_fontaineTheta (surjective_frobenius p)

theorem isDomain_preTilt : IsDomain (PreTilt (normInteger K) p) :=
  PreTilt.isDomain K NormedField.valuation (normInteger K) normInteger_integers p

end IsPerfectoidField

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]


omit [IsUltrametricDist K] in
theorem exists_norm_mem_Ioo_of_exists_pow_eq
    (h : ∀ (x : K) (n : ℕ), 0 < n → ∃ y : K, y ^ n = x) :
    ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1 := by
  intro r hr
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  set r' := max r 0 with hr'
  have hr'0 : 0 ≤ r' := le_max_right _ _
  have hr'1 : r' < 1 := max_lt hr zero_lt_one
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc0 hr'1
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hN
    exact absurd (hN.trans hc1) (lt_irrefl _)
  obtain ⟨y, hy⟩ := h c N (Nat.pos_of_ne_zero hN0)
  have hyN : ‖y‖ ^ N = ‖c‖ := by rw [← norm_pow, hy]
  refine ⟨y, lt_of_le_of_lt (le_max_left r 0) ?_, ?_⟩
  · rw [← pow_lt_pow_iff_left₀ hr'0 (norm_nonneg y) hN0, hyN]
    exact hN
  · rw [← pow_lt_one_iff_of_nonneg (norm_nonneg y) hN0, hyN]
    exact hc1

theorem of_isAlgClosed (p : ℕ) [Fact p.Prime] [CompleteSpace K] [IsAlgClosed K]
    (hp : ‖(p : K)‖ < 1) : IsPerfectoidField K p := by
  refine ⟨inferInstance, hp, ?_, ?_⟩
  · exact exists_norm_mem_Ioo_of_exists_pow_eq fun x _ hn => IsAlgClosed.exists_pow_nat_eq x hn
  · exact surjective_pow_modP_of_exists_pow_eq (Fact.out : p.Prime).ne_zero
      fun x _ => IsAlgClosed.exists_pow_nat_eq x (Fact.out : p.Prime).pos

instance padicComplex (p : ℕ) [Fact p.Prime] : IsPerfectoidField ℂ_[p] p :=
  of_isAlgClosed p (by
    have h := PadicComplex.norm_extends' p (p : ℚ_[p])
    have hc : (((p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (p : ℂ_[p]) := by
      rw [map_natCast, PadicComplex.coe_natCast]
    rw [← hc, h]
    exact Padic.norm_p_lt_one)

end IsPerfectoidField

end GroundTheory.PAdicHodge

end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial

noncomputable section

variable (p : ℕ) [Fact p.Prime]

def cycl (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  adjoin ℚ_[p] {x : PadicAlgCl p | x ^ (p ^ n) = 1}

variable {p}

theorem pow_eq_one_mem_cycl {n : ℕ} {x : PadicAlgCl p} (hx : x ^ (p ^ n) = 1) : x ∈ cycl p n :=
  subset_adjoin _ _ hx

theorem cycl_mono : Monotone (cycl p) := fun n m h =>
  adjoin.mono _ _ _ fun x (hx : x ^ (p ^ n) = 1) => by
    show x ^ (p ^ m) = 1
    obtain ⟨k, hk⟩ := Nat.pow_dvd_pow p h
    rw [hk, pow_mul, hx, one_pow]

theorem finite_setOf_pow_eq_one (n : ℕ) : {x : PadicAlgCl p | x ^ (p ^ n) = 1}.Finite := by
  classical
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine (nthRoots (p ^ n) (1 : PadicAlgCl p)).toFinset.finite_toSet.subset fun x hx => ?_
  simpa [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hpos] using hx

instance finiteDimensional_cycl (n : ℕ) : FiniteDimensional ℚ_[p] (cycl p n) := by
  haveI : Finite {x : PadicAlgCl p | x ^ (p ^ n) = 1} := (finite_setOf_pow_eq_one n).to_subtype
  exact finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) := by
  haveI : NeZero ((p ^ n : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero n (Fact.out : p.Prime).ne_zero)⟩
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic (p ^ n) (PadicAlgCl p))
    (degree_cyclotomic_pos (p ^ n) (PadicAlgCl p) hpos).ne'
  exact ⟨ζ, (isRoot_cyclotomic_iff).1 hζ⟩

theorem cycl_eq_adjoin {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    cycl p n = ℚ_[p]⟮ζ⟯ := by
  apply le_antisymm
  · rw [cycl, adjoin_le_iff]
    intro x (hx : x ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (mem_adjoin_simple_self ℚ_[p] ζ) i
  · rw [adjoin_simple_le_iff]
    exact pow_eq_one_mem_cycl hζ.pow_eq_one

theorem cycl_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n : ℕ) :
    (cycl p n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cycl p n := by
  rw [cycl, adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (σ y) ^ (p ^ n) = 1
    rw [← map_pow, show y ^ (p ^ n) = 1 from hy, map_one]
  · intro (hx : x ^ (p ^ n) = 1)
    refine ⟨σ.symm x, ?_, by simp⟩
    show (σ.symm x) ^ (p ^ n) = 1
    rw [← map_pow, hx, map_one]

end

end GroundTheory.PAdicHodge
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

theorem norm_eq_one_of_compactSpace (η : G →* ℚ_[p]ˣ) (hη : Continuous η) (σ : G) :
    ‖((η σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  set f : G → ℝ := fun τ => ‖((η τ : ℚ_[p]ˣ) : ℚ_[p])‖ with hf
  have hcont : Continuous f := (Units.continuous_val.comp hη).norm
  obtain ⟨τ₀, -, hτ₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hbound : ∀ τ, f τ ≤ f τ₀ := fun τ => hτ₀ (Set.mem_univ τ)
  have hpow : ∀ τ : G, ∀ n : ℕ, f (τ ^ n) = f τ ^ n := by
    intro τ n
    simp only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hle : ∀ τ, f τ ≤ 1 := by
    intro τ
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop (f τ₀) |>.exists
    have := hbound (τ ^ n)
    rw [hpow] at this
    linarith
  have hmul : f σ * f σ⁻¹ = 1 := by
    simp only [hf, map_inv, ← norm_mul, Units.val_inv_eq_inv_val]
    rw [mul_inv_cancel₀ (Units.ne_zero _), norm_one]
  have h0 : 0 ≤ f σ⁻¹ := norm_nonneg _
  apply le_antisymm (hle σ)
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt (hle σ⁻¹)
  linarith

theorem exists_continuous_units_padicInt_lift (η : G →* ℚ_[p]ˣ) (hη : Continuous η) :
    ∃ η' : G →* ℤ_[p]ˣ, Continuous η' ∧ ∀ σ, (((η' σ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = η σ := by
  have h1 := norm_eq_one_of_compactSpace η hη
  let η' : G →* ℤ_[p]ˣ :=
    { toFun := fun σ => PadicInt.mkUnits (h1 σ)
      map_one' := by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, map_one]
        rfl
      map_mul' := fun σ τ => by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq,
          PadicInt.mkUnits_eq, map_mul, Units.val_mul] }
  refine ⟨η', ?_, fun σ => PadicInt.mkUnits_eq (h1 σ)⟩
  have hval : Continuous fun σ => ((η σ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_val.comp hη
  have hinv : Continuous fun σ => (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) :=
    Units.continuous_val.comp (continuous_inv.comp hη)
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun σ => (⟨((η σ : ℚ_[p]ˣ) : ℚ_[p]), (h1 σ).le⟩ : ℤ_[p])
    exact hval.subtype_mk _
  · have hn : ∀ σ, ‖(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := fun σ => by
      rw [← map_inv]; exact (h1 σ⁻¹).le
    have e : (fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) =
        fun σ => (⟨(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), hn σ⟩ : ℤ_[p]) := by
      funext σ
      apply PadicInt.ext
      rw [← map_inv η' σ]
      show ((PadicInt.mkUnits (h1 σ⁻¹) : ℤ_[p]) : ℚ_[p]) = (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])
      rw [PadicInt.mkUnits_eq, map_inv]
    change Continuous fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    rw [e]
    exact hinv.subtype_mk _

end SenTateChar

end GroundTheory.PAdicHodge
end
end
