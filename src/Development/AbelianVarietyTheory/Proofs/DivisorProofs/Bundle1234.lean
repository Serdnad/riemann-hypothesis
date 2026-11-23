module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AbsHalf

theorem ordL_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hxy : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  unfold ordL
  rw [dite_eq_right hxy, dite_eq_right hx', dite_eq_right hy']
  have : WithZero.unzero hxy = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp [map_mul]
  rw [this, toAdd_mul]
  ring

theorem ordL_neg_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ordL (-1 : L) = 0 := by
  have h1 : Valued.v (-1 : L) ≠ 0 := by simp
  unfold ordL
  rw [dite_eq_right h1]
  have : WithZero.unzero h1 = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    simp only [Valuation.map_neg, Valuation.map_one]
    rfl
  rw [this]
  simp

end GlobalTheory.AbsHalf

namespace GlobalTheory.AbsHalf

theorem absHalf_mul_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x y : w.adicCompletion E, x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y) ∧
      absHalf w (-1) = 1 := by
  intro E _ _ _ w
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  refine ⟨fun x y hx hy => ?_, ?_⟩
  · unfold absHalf
    rw [ordL_mul x y hx hy, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_nonneg hq.le _)]
    push_cast
    ring
  · unfold absHalf
    rw [ordL_neg_one]
    simp

end GlobalTheory.AbsHalf
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem avg_eq_of_le_rStab : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 →
    avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ u S hS hi
  haveI : S.FiniteIndex := ⟨hi⟩
  haveI : (rStab u).FiniteIndex := Subgroup.finiteIndex_of_le hS
  have hRi : (rStab u).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hu : ∀ x : H, u ((QuotientGroup.mk x : H ⧸ rStab u).out) = u x := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
    rw [hk]
    exact k.2 x
  let e := Subgroup.quotientEquivProdOfLE hS
  have he : ∀ q : H ⧸ S, ((e q).1 : H ⧸ rStab u) = QuotientGroup.mk q.out := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  haveI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  haveI : Finite ((rStab u) ⧸ S.subgroupOf (rStab u)) := by
    have : Finite ((H ⧸ rStab u) × (rStab u) ⧸ S.subgroupOf (rStab u)) := Finite.of_equiv _ e
    exact Finite.prod_right (H ⧸ rStab u)
  haveI : Fintype ((rStab u) ⧸ S.subgroupOf (rStab u)) := Fintype.ofFinite _
  have hsum : ∑ᶠ q : H ⧸ S, u q.out =
      (S.relIndex (rStab u) : ℂ) * ∑ᶠ p : H ⧸ rStab u, u p.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    have h1 : ∀ q : H ⧸ S, u q.out = (fun p : (H ⧸ rStab u) × ((rStab u) ⧸ S.subgroupOf (rStab u)) =>
        u p.1.out) (e q) := by
      intro q
      simp only
      rw [he q, hu]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), Equiv.sum_comp e (fun p => u p.1.out),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [avg, hsum, ← Subgroup.relIndex_mul_index hS]
  have h2 : (S.relIndex (rStab u) : ℂ) ≠ 0 := by
    have : S.relIndex (rStab u) ≠ 0 := by
      intro h0; apply hi; rw [← Subgroup.relIndex_mul_index hS, h0, zero_mul]
    exact_mod_cast this
  have h3 : ((rStab u).index : ℂ) ≠ 0 := by exact_mod_cast hRi
  push_cast
  field_simp

end GlobalTheory.BCT
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PowBdd

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_le_exp (w : Pl E) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound_of_isCompact (w : Pl E) {C : Set (w.adicCompletion E)} (hC : IsCompact C) :
    ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v x ≤ B := by
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun m : ℤ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m})
    (fun m => isOpen_le_exp w m) (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases h0 : Valued.v x = 0
      · exact ⟨0, by simp [h0]⟩
      · exact ⟨WithZero.log (Valued.v x), by simp [WithZero.exp_log h0]⟩)
  refine ⟨s.sup fun m => WithZero.exp m, fun x hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact hxm.trans (Finset.le_sup (f := fun m => WithZero.exp m) hm)

end GlobalTheory.PowBdd

open GlobalTheory.PowBdd in
theorem GlobalTheory.BCT.powers_entries_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  intro E _ _ _ n w t g hc
  have hent : ∀ i j : Fin n, ∃ B : WithZero (Multiplicative ℤ), ∀ k : ℤ,
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
    intro i j
    let f : UL n w → w.adicCompletion E := fun y =>
      (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
    have hf : Continuous f := by
      have h1 : Continuous fun y : UL n w => (g⁻¹ * y * g : UL n w) :=
        (continuous_const.mul continuous_id).mul continuous_const
      have h2 : Continuous fun y : UL n w => (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
        Units.continuous_val.comp (continuous_subtype_val.comp h1)
      exact (continuous_apply j).comp ((continuous_apply i).comp h2)
    obtain ⟨B, hB⟩ := exists_bound_of_isCompact w (hc.image hf)
    refine ⟨B, fun k => hB _ ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), rfl⟩⟩
  choose B hB using hent
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => B p.1 p.2, fun k i j => ?_⟩
  exact (hB i j k).trans (Finset.le_sup (f := fun p : Fin n × Fin n => B p.1 p.2) (Finset.mem_univ (i, j)))
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem exists_nat_mul_integral_of_valuation_le : ∀ (E : Type) [Field E] [NumberField E] (γ : Pl E → WithZero (Multiplicative ℤ)), (∀ᶠ u in cofinite, γ u ≤ 1) → ∃ d : ℕ, d ≠ 0 ∧ ∀ x : E, (∀ u : Pl E, u.valuation E x ≤ γ u) → ∃ a : 𝓞 E, (a : E) = d * x := by
  intro E _ _ γ hγ
  have hfin : {u : Pl E | ¬ γ u ≤ 1}.Finite := Filter.eventually_cofinite.1 hγ
  let S : Finset (Pl E) := hfin.toFinset
  let k : Pl E → ℕ := fun u => (WithZero.log (γ u)).toNat
  let N : Pl E → ℕ := fun u => Ideal.absNorm u.asIdeal
  refine ⟨∏ u ∈ S, N u ^ k u, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro u _
    apply pow_ne_zero
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  · intro x hx
    have hval : ∀ u : Pl E, u.valuation E x * u.valuation E ((∏ w ∈ S, N w ^ k w : ℕ) : E) ≤ 1 := by
      intro u
      have hcast : (((∏ w ∈ S, N w ^ k w : ℕ) : E)) =
          algebraMap (𝓞 E) E ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) := (map_natCast _ _).symm
      rw [hcast, HeightOneSpectrum.valuation_of_algebraMap]
      by_cases hu : γ u ≤ 1
      · calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ 1 * 1 := mul_le_mul' ((hx u).trans hu) (u.intValuation_le_one _)
          _ = 1 := one_mul 1
      · have huS : u ∈ S := by
          simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hu
        have hmem : ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) ∈ u.asIdeal ^ k u := by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w => N w ^ k w) huS
          rw [hc, Nat.cast_mul]
          apply Ideal.mul_mem_right
          rw [Nat.cast_pow]
          exact Ideal.pow_mem_pow (Ideal.absNorm_mem u.asIdeal) _
        have hle := (u.intValuation_le_pow_iff_mem _ (k u)).2 hmem
        have h0 : γ u ≠ 0 := by
          intro h; exact hu (h ▸ zero_le')
        calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ γ u * WithZero.exp (-(k u : ℤ)) := mul_le_mul' (hx u) hle
          _ = WithZero.exp (WithZero.log (γ u) + -(k u : ℤ)) := by
              rw [WithZero.exp_add, WithZero.exp_log h0]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero, WithZero.exp_le_exp]
              have := Int.self_le_toNat (WithZero.log (γ u))
              simp only [k]
              omega
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (((∏ w ∈ S, N w ^ k w : ℕ) : E) * x) (fun u => by rw [map_mul, mul_comm]; exact hval u)
    exact ⟨a, by rw [← ha]⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absHalf_eq_sqrt_norm (w : Pl E) {y : w.adicCompletion E} (hy : y ≠ 0) :
    absHalf w y = ((Real.sqrt ‖y‖ : ℝ) : ℂ) := by
  have hv : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  unfold absHalf
  congr 2
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, ordL, dite_eq_right hv, neg_neg]
  simp [qV, WithZero.toAdd_unzero_eq_log]

theorem absHalf_prodFormula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E), x ≠ 0 →
    (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)).Finite ∧
      (∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x)) * ∏ v : InfinitePlace E, (‖v.embedding x‖ : ℂ) = 1 := by
  intro E _ _ _ x hx
  have key : ∀ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
      ((Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := fun w =>
    absHalf_eq_sqrt_norm w ((_root_.map_ne_zero _).mpr hx)
  have hfin : (Function.mulSupport fun w : Pl E => FinitePlace.mk w x).Finite := by
    have h0 := FinitePlace.hasFiniteMulSupport (K := E) hx
    have he : (fun w : Pl E => FinitePlace.mk w x) =
        (fun u : FinitePlace E => u x) ∘ FinitePlace.equivHeightOneSpectrum.symm := rfl
    rw [he, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h0
  have hsup : (Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x)) =
      Function.mulSupport fun w : Pl E => FinitePlace.mk w x := by
    ext w
    simp [Real.sqrt_eq_one]
  refine ⟨?_, ?_⟩
  · have hs : (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)) =
        Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
      ext w
      simp only [Function.mem_mulSupport, key, ne_eq, Complex.ofReal_eq_one]
    rw [hs, hsup]
    exact hfin
  · have hA : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) ^ 2 = ∏ᶠ w : Pl E, FinitePlace.mk w x := by
      have hfs : Function.HasFiniteMulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
        unfold Function.HasFiniteMulSupport; rw [hsup]; exact hfin
      rw [finprod_pow hfs]
      congr 1
      funext w
      exact Real.sq_sqrt (apply_nonneg _ _)
    have hF : ∏ᶠ w : Pl E, FinitePlace.mk w x = ∏ᶠ u : FinitePlace E, u x :=
      finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun u : FinitePlace E => u x)
    have hP : (∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = ∏ v : InfinitePlace E, v x ^ v.mult := by
      rw [← Finset.prod_pow]
      congr 1
      funext v
      rw [InfinitePlace.norm_embedding_eq, InfinitePlace.mult,
        if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
    have hprod := prod_abs_eq_one (K := E) hx
    have hsq : ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = 1 := by
      rw [mul_pow, hA, hP, hF, mul_comm]
      exact hprod
    have h1 : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (mul_nonneg (finprod_nonneg fun w => Real.sqrt_nonneg _)
        (Finset.prod_nonneg fun v _ => norm_nonneg _)) two_ne_zero).mp hsq
    have hc : ∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
        ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := by
      simp_rw [key]
      exact (Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm
    rw [hc]
    exact_mod_cast h1

end GlobalTheory.ProdForm
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrbCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cp_conj {n : ℕ} {w : Pl E} (g γ : UL n w) :
    (g⁻¹ * γ * g).1.val.charpoly = γ.1.val.charpoly := by
  have h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h
  rw [h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val

theorem mk_eq_iff {G : Type} [Group G] (x y : G) :
    (Quot.mk _ x : TwCl (MonoidHom.id G)) = Quot.mk _ y ↔ ∃ g : G, y = g⁻¹ * x * g := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩
    | refl a => exact ⟨1, by simp⟩
    | symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g, hg⟩ := ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩
  · rintro ⟨g, hg⟩
    exact Quot.sound ⟨g, by simpa using hg⟩

theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  refine ⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩
  haveI : Nonempty (Pl E) := ⟨w⟩
  have hspec := Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩
  refine ⟨_, ⟨?_, hspec⟩, ?_⟩
  · show _ = _
    simp only [hspec]
  · rintro u ⟨hu, hu'⟩
    rw [Set.mem_setOf_eq] at hu
    rw [hu]
    simp only [hu']

theorem ell_mul {n : ℕ} (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree) (h2 : p₂ ∈ Ell E p₂.natDegree)
    (hc : IsCoprime p₁ p₂) (hn : p₁.natDegree + p₂.natDegree = n) : p₁ * p₂ ∈ Ell E n := by
  obtain ⟨m1, -, s1, r1⟩ := h1
  obtain ⟨m2, -, s2, r2⟩ := h2
  refine ⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, Polynomial.roots_mul] at hz
  · rcases Multiset.mem_add.1 hz with h | h
    · exact r1 τ z h
    · exact r2 τ z h
  · rw [← Polynomial.map_mul]
    exact ((m1.mul m2).map τ).ne_zero

end GlobalTheory.UnitOrbCount

namespace GlobalTheory.UnitOrbCount

end GlobalTheory.UnitOrbCount
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.ClSumParam

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [map_inv, inv_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp only [map_mul, _root_.mul_inv_rev]; group⟩

theorem twCl_eq_iff (θ : G →* G) (x y : G) :
    (Quot.mk _ x : TwCl θ) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem rep_mk (θ : G →* G) (x : G) : ∃ g, TwCl.rep (θ := θ) (Quot.mk _ x) = g⁻¹ * x * θ g :=
  (twCl_eq_iff θ _ _).1 (Quot.out_eq (Quot.mk _ x : TwCl θ)).symm

theorem clSum_eq_finsum_param : ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (S : Set G)
    (f : G → ℂ) (C : Type) (ι : C → G) (N : C → ℂ), (∀ c, ι c ∈ S) → (∀ y ∈ S, ∃ c g, y = g⁻¹ * ι c * θ g) →
    (∀ c c', (∃ g, ι c' = g⁻¹ * ι c * θ g) → c = c') → (∀ y g, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) →
    (∀ y g, twOrb θ Kg (g⁻¹ * y * θ g) f = twOrb θ Kg y f) → (∀ c, twOrb θ Kg (ι c) f = N c) →
    clSum θ Kg S (fun _ => 1) f = ∑ᶠ c, N c := by
  intro G _ _ θ Kg S f C ι N hιS hsurj hinj hSinv horb hN
  let φ : C → TwCl θ := fun c => Quot.mk _ (ι c)
  have hφinj : Function.Injective φ := fun c c' h => hinj c c' ((twCl_eq_iff θ _ _).1 h)
  set F : TwCl θ → ℂ := fun c => if c.rep ∈ S then (fun _ => (1 : ℂ)) c.rep * twOrb θ Kg c.rep f else 0 with hF
  have hsupp : Function.support F ⊆ Set.range φ := by
    intro c hc
    by_contra hnot
    apply hc
    have : c.rep ∉ S := by
      intro hrep
      obtain ⟨c', g, hg⟩ := hsurj _ hrep
      apply hnot
      refine ⟨c', ?_⟩
      have h1 : (Quot.mk _ (ι c') : TwCl θ) = Quot.mk _ c.rep := (twCl_eq_iff θ _ _).2 ⟨g, hg⟩
      exact h1.trans (Quot.out_eq c)
    simp [F, this]
  have hcomp : ∀ c, F (φ c) = N c := by
    intro c
    obtain ⟨g, hg⟩ := rep_mk θ (ι c)
    have hmem : TwCl.rep (θ := θ) (φ c) ∈ S := by
      show TwCl.rep (θ := θ) (Quot.mk _ (ι c)) ∈ S
      rw [hg, hSinv]; exact hιS c
    simp only [F, if_pos hmem, one_mul]
    show twOrb θ Kg (TwCl.rep (θ := θ) (Quot.mk _ (ι c))) f = N c
    rw [hg, horb, hN]
  unfold clSum
  show ∑ᶠ c, F c = _
  rw [← finsum_congr hcomp, ← finsum_mem_range hφinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hsupp,
    finsum_mem_support]

end GlobalTheory.BCT.ClSumParam
end
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.absHalf_mul_and_absHalf_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), (∀ x y : w.adicCompletion E, x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y) ∧ absHalf w (-1) = 1 := by
  first | exact @GlobalTheory.AbsHalf.absHalf_mul_neg_one | exact GlobalTheory.AbsHalf.absHalf_mul_neg_one | (intros; apply GlobalTheory.AbsHalf.absHalf_mul_neg_one <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.avg_eq_of_le_rightStabiliser : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 → avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  first | exact @GlobalTheory.BCT.avg_eq_of_le_rStab | exact GlobalTheory.BCT.avg_eq_of_le_rStab | (intros; apply GlobalTheory.BCT.avg_eq_of_le_rStab <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.conj_zpowers_entries_valued_bounded_of_compact_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  first | exact @GlobalTheory.BCT.powers_entries_bdd | exact GlobalTheory.BCT.powers_entries_bdd | (intros; apply GlobalTheory.BCT.powers_entries_bdd <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds : ∀ (E : Type) [Field E] [NumberField E] (γ : Pl E → WithZero (Multiplicative ℤ)), (∀ᶠ u in cofinite, γ u ≤ 1) → ∃ d : ℕ, d ≠ 0 ∧ ∀ x : E, (∀ u : Pl E, u.valuation E x ≤ γ u) → ∃ a : 𝓞 E, (a : E) = d * x := by
  first | exact @GlobalTheory.exists_nat_mul_integral_of_valuation_le | exact GlobalTheory.exists_nat_mul_integral_of_valuation_le | (intros; apply GlobalTheory.exists_nat_mul_integral_of_valuation_le <;> assumption)

end
end
