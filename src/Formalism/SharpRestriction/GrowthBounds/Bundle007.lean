module

public import Formalism.SharpRestriction.GrowthBounds.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne
public import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne
public import Formalism.LocalToGlobal.CharacterGerms.Bundle015
public import Formalism.SharpRestriction.GrowthBounds.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle019
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.FrameChangePreservesMultidegree
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle022
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GenericMatrixEvaluationDet
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle014
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicLatticeCorollary
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle023
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.LinfAdjointLeEllWtHighest
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MahPadicGeOfDvd
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemBoundedDegreeExponentsIff
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_X_pow_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) f := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  rw [PowerSeries.subst_comp_subst_apply hS hS]
  congr 1
  rw [← PowerSeries.coe_substAlgHom hS, map_pow, PowerSeries.coe_substAlgHom hS, PowerSeries.subst_X hS, ← pow_mul, sq]

theorem sum_rescale_tyS_two {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) (ha : a 1 = 0) :
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (tyS l fun s => (l : C) * a (s + 2)) := by
  have e : (fun s => (l : C) * a (s + 1)) = fun s => if s < 1 then 0 else (l : C) * a (s - 1 + 2) := by
    funext s
    cases s with
    | zero => simp [ha]
    | succ s => simp
  rw [← subst_tyS_Fs hl hζ a, ← subst_X_pow_X_pow (by omega)]
  congr 1
  rw [← tyS_Vpow hl, e]

theorem sum_root_pow {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range l, (ζ ^ k) ^ (l ^ j) = (l : C) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : ∀ k, (ζ ^ k) ^ (l ^ (i + 1)) = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
  simp [h1]

theorem coeff_sum_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) (f : PowerSeries C) :
    PowerSeries.coeff (l ^ j) (∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) f) =
      (l : C) * PowerSeries.coeff (l ^ j) f := by

  rw [map_sum]
  simp only [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_root_pow hζ j hj]

section MM

variable {V : VF C}

theorem mmA_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mmA_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mmA_sum {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mmA_add) mmA_zero h

theorem mmA_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' hb ha

end MM

end SelfConjCharts

open SelfConjCharts in
theorem good_curve_closed : GoodCurveClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g a w x hG hV2
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hxT : x ∈ X.TySet V g := hG.1.1
  have hx1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2

  have hyT : Vpow 1 (fun i n => (V.l : C) * x (i + 2) n) ∈ X.TySet V g := by
    have hF := (H g).Fm x hxT
    have h3 := (H g).t3 (fun q => (RawChart.cart (H g)).c0' x q) (fun q => hG.c0'_int q)
    have hsub := (H g).add _ _ hF ((H g).neg _ h3)
    convert hsub using 1
    funext i n
    cases i with
    | zero =>
      cases n with
      | inl c => simp [Vpow, Fs, const0, hx1 c]
      | inr q => simp [Vpow, Fs, const0, Cart.c0']
    | succ i => simp [Vpow, Fs, const0]
  have hyT' := X.unV_mem V g hB.lg0 hB.exlg hζ _ hyT
  obtain ⟨γ, lam, hγ, hlam, hγ1, hγ2⟩ := id hxT
  obtain ⟨δ, -, hδ, -, hδ1, -⟩ := hyT'
  refine ⟨γ, δ, hγ, hδ, ?_, ?_, ?_⟩
  ·
    intro i
    rw [hδ1 i, hγ1 i, subst_pow_sum_smul (by positivity)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum, sum_rescale_tyS_two hl2 hζ _ (hx1 c)]
  · intro i
    rw [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1 i]
    exact mmA_sum _ _ fun c _ => MaximalIdealCongruence.mm_mul_ge' (hB.uint g c i) (hV2 c)
  · intro q
    have hA : ∀ n, PowerSeries.coeff n (alongCv γ (X.sg (X.u (1 - g) q))) =
        PowerSeries.coeff n (lam q) - PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inr q)) +
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inl c)) else 0) := by
      intro n
      have e := congrArg (PowerSeries.coeff n) (hγ2 q)

      simp only [map_add (f := _), map_sub, map_sum, apply_ite (PowerSeries.coeff n), PowerSeries.coeff_smul, map_zero,
      smul_eq_mul] at e
      linear_combination e
    have hT1 : ∀ b : ℕ → C, PowerSeries.coeff V.l (tyS V.l b) = b 1 := fun b => by
      simpa using coeff_tyS_pow hl2 b 1
    have hT2 : ∀ b : ℕ → C, PowerSeries.coeff (V.l ^ 2) (tyS V.l b) = b 2 := fun b => coeff_tyS_pow hl2 b 2
    have hN1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
        (V.l : C) * PowerSeries.coeff V.l f := fun f => by simpa using coeff_sum_rescale hζ 1 le_rfl f
    have hN2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
          (V.l : C) * PowerSeries.coeff (V.l ^ 2) f := fun f => coeff_sum_rescale hζ 2 (by norm_num) f
    have hl2pos : 0 < V.l ^ 2 := by positivity
    have hS1 : ∀ f : PowerSeries C,
        PowerSeries.coeff V.l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = 0 := fun f =>
      coeff_subst_X_pow_of_not_dvd hl2pos f V.l (fun h => by
        have := Nat.le_of_dvd hl0 h
        nlinarith)
    have hS2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) =
          PowerSeries.coeff 1 f := fun f => by simpa using coeff_subst_X_pow hl2pos f 1
    refine ⟨hG.c0'_int q, ?_, ?_⟩
    · have e : PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q =
          -((V.l : C) * PowerSeries.coeff V.l (lam q)) := by
        unfold phi
        rw [map_sub, hS1, hN1, hA]
        simp only [hT1, hx1, mul_zero, ite_self, Finset.sum_const_zero, add_zero, Cart.c0']
        ring
      rw [e]
      exact MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _))
    · have hB1 : PowerSeries.coeff 1 (alongCv δ (X.sg (X.u (1 - g) q))) =
          ∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q) := by
        rw [coeff_alongCv_low le_rfl (fun j m hm => by
            obtain rfl : m = 0 := by omega
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ j).1]) (X.constantCoeff_sg hB.axis0 _)]
        simp only [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1,
          RawChart.sg1, Finset.mul_sum, zero_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have key : (∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) -
          (V.l : C) * ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * x 2 (Sum.inl c) else 0) =
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> ring
      have e : PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q) =
          (∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q))) +
            -((V.l : C) * PowerSeries.coeff (V.l ^ 2) (lam q)) := by
        unfold phi
        rw [map_sub, hS2, hN2, hA, hB1]
        simp only [hT2]
        linear_combination key
      rw [e]
      refine mmA_add (mmA_sum _ _ fun c _ => ?_) (MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)))
      split_ifs with hm
      · exact mmA_zero
      · exact mmA_mul_int (hV2 c) (hB.hmis g c q hm)

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem exponent_condition_holds (D : Formalism.BasicNotions.D7) : adm3 D := by
  intro p hp m k b hkm hb
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.padicValNat_def]
  exact multiplicity_choose hkm hb

theorem key_positivity_condition (D : Formalism.BasicNotions.D7) : ArchimedeanSignatureMatching D := by
  intro A _ _ _ σ w hw F G h
  have hp : Prime w := UniqueFactorizationMonoid.irreducible_iff_prime.mp hw
  haveI : (Ideal.span {w}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp

  have key : ∀ H : MvPolynomial σ A,
      C w ∣ H ↔ MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {w})) H = 0 := by
    intro H
    rw [MvPolynomial.C_dvd_iff_dvd_coeff, MvPolynomial.ext_iff]
    simp only [MvPolynomial.coeff_map]
    change (∀ i, w ∣ H.coeff i) ↔ ∀ m, (Ideal.Quotient.mk (Ideal.span {w})) (H.coeff m) = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [key] at h
  rw [map_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl ((key F).mpr h1)
  · exact Or.inr ((key G).mpr h1)

private theorem sub_one_mod_eq_ite (a n : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) :
    (a - 1) % n = if 1 ≤ a % n then a % n - 1 else n - 1 := by
  have hdiv := Nat.div_add_mod a n
  have hlt := Nat.mod_lt a (by omega : n > 0)
  generalize a % n = r at hdiv hlt ⊢
  generalize a / n = q at hdiv
  generalize hx : n * q = x at hdiv
  split_ifs with hr
  · have e : a - 1 = (r - 1) + x := by omega
    rw [e, ← hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have hq : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hx
      omega
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    have hx' : x = n * q' + n := by rw [← hx, Nat.mul_succ]
    generalize hy : n * q' = y at hx'
    have e : a - 1 = (n - 1) + y := by omega
    rw [e, ← hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem true_derivative_digit_class (D : Formalism.BasicNotions.D7) : TrueDerivativeDigitClass D := by
  classical
  intro R _ σ P hP rho k F hF
  have hF' : ∀ m ∈ F.support, digitOfL P m = rho := fun m hm =>
    (show (↑F.support : Set (σ →₀ ℕ)) ⊆ {m | digitOfL P m = rho} from hF) hm

  rw [F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.pderiv_monomial, DigitClassL, MvPolynomial.monomial_mem_restrictSupport]
  by_cases hmk : m k = 0
  · right
    simp [hmk]
  · left
    have hd := hF' m hm
    show digitOfL P (m - Finsupp.single k 1) = _
    funext j
    have hdj := congrFun hd j
    simp only [digitOfL] at hdj ⊢
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_self, Finsupp.tsub_apply, Finsupp.single_eq_same,
        sub_one_mod_eq_ite (m j) (P j) (hP j) (Nat.one_le_iff_ne_zero.mpr hmk), hdj]
    · rw [Function.update_of_ne hjk, Finsupp.tsub_apply]
      simp [Ne.symm hjk, hdj]

theorem unit_function_expansion (D : Formalism.BasicNotions.D7) : UnitFunctionExpansion D := mahler_decay_products_of D (fun p hp => hDec_of hp (hdU_proved hp)) (fun p hp => hMul_proved hp)

theorem lemma_five_two_first_holds (D : Formalism.BasicNotions.D7) : FactorialUnitDecomposition D := unit_function_mahler_decay_of D (fun p hp => hDec_of hp (hdU_proved hp)) (fun p hp => hMul_proved hp)
    (fun p hp => hUnit_of hp (hdU_proved hp))

theorem support_coprimality_lemma_holds (D : Formalism.BasicNotions.D7) : ConclusionE D := prvE_of_gl_operators_form_representation D (height_bound_of_weights hSupp_proved hCop_proved)

theorem section_five_lemmas_hold (D : Formalism.BasicNotions.D7) : UnitProductLemmas D := ⟨unit_function_expansion D, show FactorialUnitDecomposition D ∧ DegreeTruncationLemma D from ⟨lemma_five_two_first_holds D, degree_truncation D⟩⟩

theorem lattice_index_lemma_holds (D : Formalism.BasicNotions.D7) : DerivativeLemmaField D := show DerivativeValuationBound D ∧ DerivativeDigitExpansion D ∧ TrueDerivativeDigitClass D from ⟨derivative_valuation_bound D, derivative_digit_expansion D, true_derivative_digit_class D⟩

theorem valuation_field_of_adm2 (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : ValuationLemmaField D := show ValuationsAdditive D ∧ ShaLengthVersionTwo D from ⟨valuationsAdditive_D7 D, generated_weight_lemma_of_reducibility D h2 (valuationsAdditive_D7 D)⟩

theorem valuation_field (D : Formalism.BasicNotions.D7) : ValuationLemmaField D := valuation_field_of_adm2 D (weight_condition_from_integral_form D)

theorem invariant_projection_sup_norm_denominator (D : Formalism.BasicNotions.D7) : InvariantDenominatorLinftyBound := linf_lemma_without_projector D (weight_condition_from_integral_form D)

theorem invariantProjectionDenominator (D : Formalism.BasicNotions.D7) : InvariantProjectionDenominator := denominator_lemma_without_projector D (weight_condition_from_integral_form D)

theorem nabla_delta_comparison_field (D : Formalism.BasicNotions.D7) : NablaDeltaComparisonField D := integral_form_of_linf_lemma D (weight_condition_from_integral_form D) (invariant_projection_sup_norm_denominator D)

theorem isotypic_projector_theorem_field (D : Formalism.BasicNotions.D7) : IsotypicProjectorTheoremField D := isotypicProjectorTheoremField_of_linfty_bound D (weight_condition_from_integral_form D) (invariant_projection_sup_norm_denominator D)

theorem translate_corollary_field (D : Formalism.BasicNotions.D7) : TranslateCorollaryField D := isotypic_lattice_corollary D (weight_condition_from_integral_form D) (nabla_delta_comparison_field D)

theorem filtered_projector_corollary_field (D : Formalism.BasicNotions.D7) : FilteredProjectorCorollaryField D := polynomial_isotypic_lattice_corollary D (weight_condition_from_integral_form D) (isotypic_projector_theorem_field D)

def InvariantProductFormula : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        (∀ π : Module.End (KK O) V, IsWtProj E 0 π → ∀ ord, NormalOrder n ord →
          ∀ T : ℕ, Module.finrank (KK O) V ≤ T → Inv = pp E 0 ord T * π)

theorem invariant_projection_of_product_formula (D : Formalism.BasicNotions.D7) (h : InvariantProductFormula) : InvariantProjectionField D := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv
  exact ⟨h p n' O S hG n V E hE M hM hMQ Inv hInv, invariantProjectionDenominator D p n' O S hG n V E hE M hM hMQ Inv hInv⟩

theorem product_formula_of_extremal_projector (D : Formalism.BasicNotions.D7) (h5 : adm5 D) : InvariantProductFormula := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv π hπ ord hord T hT
  haveI := dvr_fraction_field_charZero_prime S hG.prime
  exact invariant_projection_extremal_formula D (weight_condition_from_integral_form D) h5 E hE Inv hInv π hπ ord hord T hT

theorem counting_statement_of_block_form (D : Formalism.BasicNotions.D7) (h : InvariantProductFormula) : Conclusion1 D := show ProjectionTheorems D ∧ ValuationLemmaField D ∧ ConclusionE D ∧ UnitProductLemmas D ∧ DerivativeLemmaField D from
    ⟨show InvariantProjectionField D ∧ NablaDeltaComparisonField D ∧ IsotypicProjectorTheoremField D ∧ TranslateCorollaryField D ∧ FilteredProjectorCorollaryField D from
      ⟨invariant_projection_of_product_formula D h, nabla_delta_comparison_field D, isotypic_projector_theorem_field D, translate_corollary_field D, filtered_projector_corollary_field D⟩,
     valuation_field D, support_coprimality_lemma_holds D, section_five_lemmas_hold D, lattice_index_lemma_holds D⟩

theorem part_one_of_extremal_projector (D : Formalism.BasicNotions.D7) (h5 : adm5 D) : Conclusion1 D := counting_statement_of_block_form D (product_formula_of_extremal_projector D h5)

theorem problem_holds (D : Formalism.BasicNotions.D7) : IntegralityFromMetric D := fun hA => part_one_of_extremal_projector D (show admitted D from hA).2.2.2.2

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

theorem nested_sets_lemma_of_admitted (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) (h16 : PairedPathIndependence D) : ConclusionB3 D :=
  lemma_B3 D h16 (lemma_B2 D) (integral_joint_type_sum D h14 h16)

end Formalism.MainNotions.LemmaBAlt
end
end
