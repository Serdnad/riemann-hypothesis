module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Polynomial

namespace GlobalTheory.QFam

theorem vieta_root {ι : Type} [Fintype ι] (y : ι → ℂ) (i : ι) :
    y i ^ Fintype.card ι + ∑ j : Fin (Fintype.card ι),
      ((-1) ^ (Fintype.card ι - (j : ℕ)) *
        ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, y l) *
        y i ^ (j : ℕ) = 0 := by
  classical
  set n := Fintype.card ι with hn
  set P : ℂ[X] := ∏ l, (X + C (-y l)) with hP
  have hmon : P.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_add_C _
  have hdeg : P.natDegree = n := by
    rw [hP, natDegree_prod_of_monic _ _ fun l _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn]
  have hroot : P.eval (y i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hcoeff : ∀ j ≤ n, P.coeff j =
      (-1) ^ (n - j) * ∑ t ∈ Finset.powersetCard (n - j) Finset.univ, ∏ l ∈ t, y l := by
    intro j hj
    rw [hP, Finset.prod_X_add_C_coeff _ _ (by simpa [hn] using hj), Finset.card_univ, ← hn,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]
  have h1 : P.coeff n = 1 := hdeg ▸ hmon.coeff_natDegree
  rw [eval_eq_sum_range, hdeg, Finset.sum_range_succ, h1, one_mul] at hroot
  rw [← hroot, add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * y i ^ m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoeff j j.2.le]

end GlobalTheory.QFam

theorem GlobalTheory.QFam.minpoly_coeff_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (k N : ℕ) (F : ι → ℍ → ℂ) (R : Subring ℂ), 0 < N → ActBij act → IsFam act k F → (∀ i, QAll (· ∈ R) N (F i)) → ∃ s : Fin (Fintype.card ι) → ℍ → ℂ, (∀ j : Fin (Fintype.card ι), (∀ γ : SL(2, ℤ), s j ∣[((k * (Fintype.card ι - j) : ℕ) : ℤ)] γ = s j) ∧ QAll (· ∈ R) N (s j)) ∧ ∀ i τ, F i τ ^ Fintype.card ι + ∑ j, s j τ * F i τ ^ (j : ℕ) = 0 := by
  intro ι _ act k N F R _ hb hF hQ
  refine ⟨fun j τ => (-1) ^ (Fintype.card ι - (j : ℕ)) *
      ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, F l τ,
    fun j => ⟨fun γ => ?_, ?_⟩, fun i τ => vieta_root (fun l => F l τ) i⟩
  · have hE := IsFam.esymm_slash hb hF γ (Fintype.card ι - (j : ℕ))
    have hw : (((k * (Fintype.card ι - (j : ℕ)) : ℕ) : ℤ)) =
        (((Fintype.card ι - (j : ℕ) : ℕ) : ℤ) * (k : ℤ)) := by
      rw [Nat.cast_mul, mul_comm]
    funext τ
    have hEτ := congrFun hE τ
    rw [ModularForm.SL_slash_apply] at hEτ
    rw [hw, ModularForm.SL_slash_apply, mul_assoc, hEτ]
  · exact QAllSubring.mul (QAllSubring.const (R.pow_mem (R.neg_mem R.one_mem) _))
      (QAllSubring.sum _ fun t _ => QAllSubring.prod _ fun l _ => hQ l)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Function

namespace GlobalTheory.FN

theorem periodic_comp_ofComplex_of_vadd_real {f : ℍ → ℂ} {h : ℝ}
    (hf : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) (h : ℂ) := by
  intro w
  by_cases! hw : 0 < Complex.im w
  · have : 0 < Complex.im (w + h) := by simp [hw]
    simp only [comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos this,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    convert! hf ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have : Complex.im (w + h) ≤ 0 := by simpa using hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos this,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw]

theorem hasQ_of_periodic_bounded : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  intro N f hN hf hper hbdd
  refine ⟨fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion (N : ℝ) f), ?_⟩
  rw [GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
  exact GlobalTheory.HasQExpansion.of_periodic (by exact_mod_cast hN)
    (periodic_comp_ofComplex_of_vadd_real hper) hf hbdd

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.QFam.LagrangeFam

def esymmOff {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι → ℍ → ℂ) (j : ℕ) (i : ι) (τ : ℍ) : ℂ :=
  ∑ s ∈ Finset.powersetCard j (Finset.univ.erase i), ∏ l ∈ s, t l τ

def lagCoeff {ι : Type} [Fintype ι] [DecidableEq ι] (t F : ι → ℍ → ℂ) (j : ℕ) (τ : ℍ) : ℂ :=
  (-1) ^ j * ∑ i, F i τ * esymmOff t j i τ

theorem prod_sub_eq_sum {κ : Type} (s : Finset κ) (y : κ → ℂ) (x : ℂ) :
    ∏ l ∈ s, (x - y l) = ∑ j ∈ Finset.range (s.card + 1),
      (-1) ^ j * (∑ u ∈ Finset.powersetCard j s, ∏ l ∈ u, y l) * x ^ (s.card - j) := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm (s.val.map y))
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Multiset.card_map,
    Finset.esymm_map_val] at h
  rw [Finset.prod_eq_multiset_prod]
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.card_val]
  ring

theorem lag_eval {ι : Type} [Fintype ι] [DecidableEq ι] (t F : ι → ℍ → ℂ) (i : ι) (τ : ℍ) :
    F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) =
      ∑ j ∈ Finset.range (Fintype.card ι), lagCoeff t F j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  have hc : ∀ i' : ι, (Finset.univ.erase i').card + 1 = Fintype.card ι := fun i' => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i'⟩
    omega
  have hc' : ∀ i' : ι, (Finset.univ.erase i').card = Fintype.card ι - 1 := fun i' => by
    have := hc i'; omega
  have key : ∀ i' : ι, F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) =
      ∑ j ∈ Finset.range (Fintype.card ι),
        (-1) ^ j * (F i' τ * esymmOff t j i' τ) * t i τ ^ (Fintype.card ι - 1 - j) := by
    intro i'
    rw [prod_sub_eq_sum, hc i', hc' i', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [esymmOff]
    ring
  have hz : ∀ i' ∈ (Finset.univ : Finset ι), i' ≠ i →
      F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) = 0 := by
    intro i' _ hne
    rw [Finset.prod_eq_zero (i := i) (Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩)
      (sub_self _), mul_zero]
  rw [← Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hz]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [lagCoeff, Finset.mul_sum, Finset.sum_mul]

theorem esymmOff_value {ι : Type} [Fintype ι] [DecidableEq ι] {act : ι → SL(2, ℤ) → ι} {m : ℕ}
    {t : ι → ℍ → ℂ} (hb : ActBij act) (ht : IsFam act m t) (γ : SL(2, ℤ)) (j : ℕ) (i : ι)
    (τ : ℍ) :
    esymmOff t j i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) =
      esymmOff t j (act i γ) τ := by
  unfold esymmOff
  rw [Finset.sum_mul]
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  have he : ∀ l, e l = act l γ := fun l => rfl
  refine Finset.sum_equiv e.finsetCongr (fun s => ?_) (fun s hs => ?_)
  · simp only [Finset.mem_powersetCard, Equiv.finsetCongr_apply, Finset.card_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, h2⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have := h1 hy
      rw [Finset.mem_erase] at this ⊢
      refine ⟨fun h => this.1 ?_, Finset.mem_univ _⟩
      rw [← he] at h
      exact e.injective h
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, h2⟩
      have := h1 (Finset.mem_map_of_mem e.toEmbedding hx)
      rw [Finset.mem_erase] at this ⊢
      exact ⟨fun h => this.1 (by rw [Equiv.coe_toEmbedding, h]; rfl), Finset.mem_univ _⟩
  · have hc : s.card = j := (Finset.mem_powersetCard.mp hs).2
    have h1 : UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) =
        ∏ _l ∈ s, UpperHalfPlane.denom γ τ ^ (-(m : ℤ)) := by
      rw [Finset.prod_const, hc, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [h1, ← Finset.prod_mul_distrib, Equiv.finsetCongr_apply, Finset.prod_map]
    exact Finset.prod_congr rfl fun l _ => ht.value_mul_denom l γ τ

theorem lagCoeff_slash {ι : Type} [Fintype ι] [DecidableEq ι] {act : ι → SL(2, ℤ) → ι} {m k : ℕ}
    {t F : ι → ℍ → ℂ} (hb : ActBij act) (ht : IsFam act m t) (hF : IsFam act k F) (j : ℕ)
    (γ : SL(2, ℤ)) :
    lagCoeff t F j ∣[((k + m * j : ℕ) : ℤ)] γ = lagCoeff t F j := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  unfold lagCoeff
  have hD : UpperHalfPlane.denom γ τ ^ (-(((k + m * j : ℕ) : ℤ))) =
      UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ τ)]
    congr 1
    push_cast
    ring
  rw [hD, mul_assoc, Finset.sum_mul]
  congr 1
  have : ∀ i, F i (γ • τ) * esymmOff t j i (γ • τ) *
      (UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ))) =
      F (act i γ) τ * esymmOff t j (act i γ) τ := fun i => by
    rw [← hF.value_mul_denom i γ τ, ← esymmOff_value hb ht γ j i τ]
    ring
  simp only [this]
  exact (hb γ).sum_comp (fun i => F i τ * esymmOff t j i τ)

theorem lagrange_fam : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (act : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t F : ι → ℍ → ℂ), 0 < N → ActBij act → IsFam act m t → IsFam act k F → (∀ i, ∃ a, HasQ N (t i) a) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ c : ℕ → ℍ → ℂ, (∀ j, (∀ γ : SL(2, ℤ), c j ∣[((k + m * j : ℕ) : ℤ)] γ = c j) ∧ ∃ a, HasQ N (c j) a) ∧ ∀ i τ, F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) = ∑ j ∈ Finset.range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  intro ι _ _ act m k N t F _ hb ht hF hqt hqF
  refine ⟨lagCoeff t F, fun j => ⟨fun γ => lagCoeff_slash hb ht hF j γ, ?_⟩,
    fun i τ => lag_eval t F i τ⟩
  have qt : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (t i) := fun i =>
    let ⟨a, ha⟩ := hqt i; ⟨a, ha, fun _ => Subring.mem_top _⟩
  have qF : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (F i) := fun i =>
    let ⟨a, ha⟩ := hqF i; ⟨a, ha, fun _ => Subring.mem_top _⟩
  have hq : QAll (· ∈ (⊤ : Subring ℂ)) N (lagCoeff t F j) :=
    QAllSubring.mul (QAllSubring.const (Subring.mem_top ((-1 : ℂ) ^ j)))
      (QAllSubring.sum _ fun i _ => QAllSubring.mul (qF i)
        (QAllSubring.sum _ fun s _ => QAllSubring.prod s fun l _ => qt l))
  obtain ⟨a, ha, _⟩ := hq
  exact ⟨a, ha⟩

end GlobalTheory.QFam.LagrangeFam
end
end
