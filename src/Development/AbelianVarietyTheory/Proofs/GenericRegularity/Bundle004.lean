module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Smooth.Basic
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
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

section

namespace GlobalTheory

open IsLocalRing


open IsLocalRing in
theorem _root_.GlobalTheory.dvr_finite_over_complete_dvr :
    ∀ (O V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing V] [IsDomain V]
      [IsDiscreteValuationRing V] [Algebra O V] [Module.Finite O V],
      Function.Injective (algebraMap O V) ∧ IsLocalHom (algebraMap O V) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V ∧
          (Finite (IsLocalRing.ResidueField O) → Finite (IsLocalRing.ResidueField V)) := by
  intro O V _ _ _ _ _ _ _ _ _ _
  haveI : Algebra.IsIntegral O V := Algebra.IsIntegral.of_finite O V
  have hinj : Function.Injective (algebraMap O V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    by_contra h
    push_neg at h
    obtain ⟨a, ha, ha0⟩ := h
    have hker : (RingHom.ker (algebraMap O V)).IsMaximal := by
      refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
      intro hb
      apply ha0
      have hmem : a ∈ RingHom.ker (algebraMap O V) := ha
      rw [hb] at hmem
      exact (Ideal.mem_bot).1 hmem
    have hbot : (⊥ : Ideal V).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) ⊥
        (by rwa [Ideal.under_def, ← RingHom.ker_eq_comap_bot])
    exact IsDiscreteValuationRing.not_a_field V (IsLocalRing.eq_maximalIdeal hbot).symm
  have hloc : IsLocalHom (algebraMap O V) :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  haveI := hloc
  refine ⟨hinj, hloc, ?_, charZero_of_injective_algebraMap hinj, fun h => ?_⟩
  swap
  · exact Module.finite_of_finite (ResidueField O)
  haveI : Module.IsTorsionFree O V := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπm : π ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hπ.not_isUnit)
  have hp0 : algebraMap O V π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpm : algebraMap O V π ∈ maximalIdeal V :=
    (mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => hπ.not_isUnit ((isUnit_map_iff _ _).1 hu))
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap O V π}) (by simpa using hp0) hq
  have hpow : ∀ k, maximalIdeal V ^ (e * k) = Ideal.span {algebraMap O V π ^ k} := by
    intro k
    rw [hq.maximalIdeal_eq, Ideal.span_singleton_pow, pow_mul, ← Ideal.span_singleton_pow, ← he,
      Ideal.span_singleton_pow]
  refine
    { toIsHausdorff := IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal V).ne_top
      toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  have hf' : ∀ m n, m ≤ n → f m - f n ∈ maximalIdeal V ^ m := fun m n h => by
    simpa using SModEq.sub_mem.1 (hf h)
  have hg : ∀ m n, m ≤ n →
      ∃ y, f (e * m + m) - f (e * n + n) = algebraMap O V π ^ m * y := by
    intro m n h
    have h1 := hf' _ _ (Nat.add_le_add (Nat.mul_le_mul_left e h) h)
    have h2 : f (e * m + m) - f (e * n + n) ∈ Ideal.span {algebraMap O V π ^ m} := by
      rw [← hpow]
      exact Ideal.pow_le_pow_right (Nat.le_add_right _ _) h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨y, by rw [← hy, mul_comm]⟩
  let b := Module.Free.chooseBasis O V
  have hc : ∀ i, ∀ {m n : ℕ}, m ≤ n →
      b.repr (f (e * m + m)) i ≡ b.repr (f (e * n + n)) i
        [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    intro i m n h
    obtain ⟨y, hy⟩ := hg m n h
    have hdiff : b.repr (f (e * m + m)) i - b.repr (f (e * n + n)) i = π ^ m * b.repr y i := by
      rw [← Finsupp.sub_apply, ← map_sub, hy, ← map_pow, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, smul_eq_mul]
    have hmem : π ^ m * b.repr y i ∈ maximalIdeal O ^ m :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm m)
    rw [SModEq.sub_mem, hdiff]
    simpa using hmem
  choose l hl using fun i =>
    (inferInstance : IsPrecomplete (maximalIdeal O) O).prec
      (f := fun k => b.repr (f (e * k + k)) i) (hc i)
  refine ⟨∑ i, l i • b i, fun n => ?_⟩
  have hgn : f (e * n + n) - ∑ i, l i • b i ∈ maximalIdeal V ^ n := by
    have hex : ∀ i, ∃ t, b.repr (f (e * n + n)) i - l i = π ^ n * t := fun i => by
      have hmem := SModEq.sub_mem.1 (hl i n)
      simp only [smul_eq_mul, Ideal.mul_top] at hmem
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, by rw [← ht, mul_comm]⟩
    choose t ht using hex
    have hsum : f (e * n + n) - ∑ i, l i • b i =
        algebraMap O V π ^ n * ∑ i, t i • b i := by
      conv_lhs => rw [← b.sum_repr (f (e * n + n))]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ht, mul_smul, Algebra.smul_def, map_pow]
    rw [hsum]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm n)
  have hfg : f n - f (e * n + n) ∈ maximalIdeal V ^ n := hf' n (e * n + n) (Nat.le_add_left _ _)
  have hsum := Ideal.add_mem _ hfg hgn
  rw [sub_add_sub_cancel] at hsum
  rw [SModEq.sub_mem]
  simpa using hsum

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

def compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : ValuationSubring L where
  toSubring := (V.toSubring.comap (residue W)).map W.subtype
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x⁻¹ ∈ W
      · rcases eq_or_ne x 0 with rfl | hx0
        · exact Or.inl (Subring.zero_mem _)
        have hmul : residue W ⟨x, hx⟩ * residue W ⟨x⁻¹, hx'⟩ = 1 := by
          rw [← map_mul, ← map_one (residue W)]
          congr 1
          exact Subtype.ext (mul_inv_cancel₀ hx0)
        rcases V.mem_or_inv_mem (residue W ⟨x, hx⟩) with h | h
        · exact Or.inl ⟨⟨x, hx⟩, h, rfl⟩
        · refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
          rw [← eq_inv_of_mul_eq_one_right hmul] at h
          exact h
      · refine Or.inl ⟨⟨x, hx⟩, ?_, rfl⟩
        have hm : (⟨x, hx⟩ : W) ∈ maximalIdeal W := by
          rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
          exact Or.inr hx'
        have h0 : residue W ⟨x, hx⟩ = 0 := (residue_eq_zero_iff _).2 hm
        change residue W ⟨x, hx⟩ ∈ V
        rw [h0]
        exact V.zero_mem
    · have hx' : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hx
      refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
      have hm : (⟨x⁻¹, hx'⟩ : W) ∈ maximalIdeal W := by
        rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
        exact Or.inr (by simpa using hx)
      have h0 : residue W ⟨x⁻¹, hx'⟩ = 0 := (residue_eq_zero_iff _).2 hm
      change residue W ⟨x⁻¹, hx'⟩ ∈ V
      rw [h0]
      exact V.zero_mem

theorem mem_compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) (x : L) :
    x ∈ compositeValuationSubring W V ↔ ∃ h : x ∈ W, residue W ⟨x, h⟩ ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hV⟩
    exact ⟨⟨x, h⟩, hV, rfl⟩

theorem compositeValuationSubring_le {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : compositeValuationSubring W V ≤ W :=
  fun x hx => ((mem_compositeValuationSubring W V x).1 hx).1

theorem exists_valuationSubring_le_dominating {O L : Type*} [CommRing O] [IsLocalRing O]
    [Field L] (g : O →+* L) (W : ValuationSubring L) (hg : ∀ x, g x ∈ W) :
    ∃ W' : ValuationSubring L, W' ≤ W ∧ (∀ x : O, g x ∈ W') ∧
      ∀ x ∈ maximalIdeal O, g x ∈ W'.nonunits := by
  let g' : O →+* W := g.codRestrict W.toSubring hg
  let f : O →+* ResidueField W := (residue W).comp g'
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨compositeValuationSubring W V, compositeValuationSubring_le W V, fun x =>
    (mem_compositeValuationSubring W V _).2 ⟨hg x, hV x⟩, fun x hx => ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_or]
  rcases eq_or_ne (g x) 0 with h0 | h0
  · exact Or.inl h0
  refine Or.inr fun hinv => ?_
  obtain ⟨h, hres⟩ := (mem_compositeValuationSubring W V _).1 hinv
  have hmul : f x * residue W ⟨(g x)⁻¹, h⟩ = 1 := by
    change residue W (g' x) * _ = 1
    rw [← map_mul, ← map_one (residue W)]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ h0)
  have hu : IsUnit (f.codRestrict V.toSubring hV x) :=
    isUnit_iff_exists_inv.2 ⟨⟨_, hres⟩, Subtype.ext hmul⟩
  exact (mem_maximalIdeal x).1 hx (hloc.1 x hu)

theorem exists_valuationSubring_le_dominating_of_fractionField :
    ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
      [Algebra O F] [IsFractionRing O F] [Field L] (ι : F →+* L) (W : ValuationSubring L),
      (∀ x, ι x ∈ W) → ∃ W' : ValuationSubring L, W' ≤ W ∧
        (∀ x : O, ι (algebraMap O F x) ∈ W') ∧
        ∀ x ∈ IsLocalRing.maximalIdeal O, ι (algebraMap O F x) ∈ W'.nonunits := by
  intro O F L _ _ _ _ _ _ _ ι W hW
  exact exists_valuationSubring_le_dominating (ι.comp (algebraMap O F)) W fun x => hW _

end GlobalTheory
end

section

namespace GlobalTheory

open MvPolynomial

section PolyChart

variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)

noncomputable def polyChartHom :
    MvPolynomial V R₀ →ₐ[K] FractionRing (MvPolynomial V F₀) :=
  (IsScalarTower.toAlgHom K (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))).comp
    (MvPolynomial.mapAlgHom R₀.val)

theorem polyChartHom_apply (p : MvPolynomial V R₀) :
    polyChartHom V R₀ p = algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (MvPolynomial.map (R₀.val : R₀ →+* F₀) p) := rfl

theorem polyChartHom_injective : Function.Injective (polyChartHom V R₀) := by
  intro p q h
  rw [polyChartHom_apply, polyChartHom_apply] at h
  exact MvPolynomial.map_injective _ Subtype.val_injective
    (IsFractionRing.injective (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) h)

theorem polyChartHom_C (a : R₀) :
    polyChartHom V R₀ (C a) = algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a := by
  rw [polyChartHom_apply, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply F₀ (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))]
  rfl

theorem polyChartHom_X (v : V) :
    polyChartHom V R₀ (X v) =
      algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v) := by
  rw [polyChartHom_apply, MvPolynomial.map_X]

theorem polyChartHom_range :
    (polyChartHom V R₀).range = Algebra.adjoin K
      ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪
        Set.range fun v : V =>
          algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v)) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change polyChartHom V R₀ p ∈ _
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [polyChartHom_C]
      exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul, polyChartHom_X]
      exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨v, rfl⟩))
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨C ⟨a, ha⟩, polyChartHom_C V R₀ ⟨a, ha⟩⟩
    · exact ⟨X v, polyChartHom_X V R₀ v⟩

theorem polyChart_clear (h : ∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a)
    (p : MvPolynomial V F₀) :
    ∃ b : R₀, (b : F₀) ≠ 0 ∧ ∃ q : MvPolynomial V R₀,
      p * C (b : F₀) = MvPolynomial.map (R₀.val : R₀ →+* F₀) q := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h x
    refine ⟨⟨b, hb⟩, hb0, C ⟨a, ha⟩, ?_⟩
    rw [MvPolynomial.map_C, ← map_mul]
    exact congrArg C e
  | add p q hp hq =>
    obtain ⟨b, hb, p', e⟩ := hp
    obtain ⟨c, hc, q', f⟩ := hq
    refine ⟨b * c, mul_ne_zero hb hc, p' * C c + q' * C b, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e, ← f]
    change (p + q) * C ((b : F₀) * c) = p * C (b : F₀) * C (c : F₀) + q * C (c : F₀) * C (b : F₀)
    rw [map_mul]
    ring
  | mul_X p v hp =>
    obtain ⟨b, hb, p', e⟩ := hp
    refine ⟨b, hb, p' * X v, ?_⟩
    rw [map_mul, MvPolynomial.map_X, ← e]
    ring

end PolyChart

theorem polyChart_smooth_fraction_lift : ∀ (K F₀ V : Type) [Field K] [Field F₀] [Algebra K F₀] [Finite V] (R₀ : Subalgebra K F₀) (R : Subalgebra K (FractionRing (MvPolynomial V F₀))), R = Algebra.adjoin K ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪ Set.range fun v : V => algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v)) → (Algebra.Smooth K R₀ → Algebra.Smooth K R) ∧ ((∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∀ x : FractionRing (MvPolynomial V F₀), ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) ∧ ∀ (S : Type) [CommRing S] [Algebra K S] (ψ : R₀ →ₐ[K] S) (t : V → S), ∃! ψ' : R →ₐ[K] S, (∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈ R), ψ' ⟨_, h⟩ = ψ a) ∧ ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v) ∈ R), ψ' ⟨_, h⟩ = t v := by
  intro K F₀ V _ _ _ _ R₀ R hR
  rw [← polyChartHom_range] at hR
  subst hR
  let e : MvPolynomial V R₀ ≃ₐ[K] (polyChartHom V R₀).range :=
    AlgEquiv.ofInjective _ (polyChartHom_injective V R₀)
  have he : ∀ p, ((e p : (polyChartHom V R₀).range) : FractionRing (MvPolynomial V F₀))
      = polyChartHom V R₀ p := fun p => rfl
  have heC : ∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
      (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (C a) :=
    fun a h => Subtype.ext (polyChartHom_C V R₀ a).symm
  have heX : ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (X v) ∈ (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (X v) :=
    fun v h => Subtype.ext (polyChartHom_X V R₀ v).symm
  refine ⟨fun hs => ?_, fun h x => ?_, fun S _ _ ψ t => ?_⟩
  · have : Algebra.Smooth R₀ (MvPolynomial V R₀) := ⟨inferInstance, inferInstance⟩
    have : Algebra.Smooth K (MvPolynomial V R₀) := Algebra.Smooth.comp K R₀ _
    exact Algebra.Smooth.of_equiv e
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial V F₀) x
    obtain ⟨b, hb, p', e1⟩ := polyChart_clear V R₀ h p
    obtain ⟨c, hc, q', e2⟩ := polyChart_clear V R₀ h q
    have hq0 : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    have hne : ∀ d : F₀, d ≠ 0 →
        algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (C d) ≠ 0 := by
      intro d hd h0
      rw [IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero] at h0
      exact hd h0
    have h1 : polyChartHom V R₀ (p' * C c) =
        algebraMap (MvPolynomial V F₀) _ (p * C (b : F₀) * C (c : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e1]; rfl
    have h2 : polyChartHom V R₀ (q' * C b) =
        algebraMap (MvPolynomial V F₀) _ (q * C (c : F₀) * C (b : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e2]; rfl
    refine ⟨_, ⟨_, h1⟩, _, ⟨_, h2⟩, ?_, ?_⟩
    · rw [map_mul, map_mul]
      exact mul_ne_zero (mul_ne_zero hq0 (hne _ hc)) (hne _ hb)
    · simp only [map_mul]
      field_simp
  · let φ : MvPolynomial V R₀ →ₐ[K] S := MvPolynomial.aevalTower ψ t
    refine ⟨φ.comp e.symm.toAlgHom, ⟨fun a h => ?_, fun v h => ?_⟩, ?_⟩
    · rw [heC]
      simp [φ]
    · rw [heX]
      simp [φ]
    · rintro χ ⟨hC, hX⟩
      have : χ.comp e.toAlgHom = φ := by
        apply MvPolynomial.algHom_ext'
        · ext a
          have hm : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
            (polyChartHom V R₀).range := ⟨C a, polyChartHom_C V R₀ a⟩
          have := (congrArg χ (heC a hm)).symm.trans (hC a hm)
          simpa [φ] using this
        · intro v
          have hm : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
            (X v) ∈ (polyChartHom V R₀).range := ⟨X v, polyChartHom_X V R₀ v⟩
          have := (congrArg χ (heX v hm)).symm.trans (hX v hm)
          simpa [φ] using this
      rw [← this]
      ext x
      simp

end GlobalTheory
end

section

namespace GlobalTheory

theorem adjoin_ratios_of_span_eq_top :
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω) (m : ℕ) (w : Fin m → R) (k : Fin m), Ideal.span (Set.range w) = ⊤ → (w k : Ω) ≠ 0 → ∀ R' : Subalgebra K Ω, R' = Algebra.adjoin K ((R : Set Ω) ∪ Set.range fun i => (w i : Ω) / (w k : Ω)) → ∃ h : R ≤ R', (w k : Ω)⁻¹ ∈ R' ∧ (Algebra.Smooth K R → Algebra.Smooth K R') ∧ ∀ (L : Type) [Field L] [Algebra K L] (ψ : R →ₐ[K] L), ψ (w k) ≠ 0 → ∃ ψ' : R' →ₐ[K] L, ψ'.comp (Subalgebra.inclusion h) = ψ ∧ ∀ i (hi : (w i : Ω) / (w k : Ω) ∈ R'), ψ' ⟨_, hi⟩ = ψ (w i) / ψ (w k) := by
  intro K Ω _ _ _ R m w k hspan hk R' hR'
  have h : R ≤ R' := by
    rw [hR']; intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
  have hrat : ∀ i, (w i : Ω) / (w k : Ω) ∈ R' := by
    intro i; rw [hR']; exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  have hinv : (w k : Ω)⁻¹ ∈ R' := by
    have h1 : (1 : R) ∈ Ideal.span (Set.range w) := by rw [hspan]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
    have h2 : ∑ i, (a i : Ω) * (w i : Ω) = 1 := by
      have := congrArg (fun x : R => (x : Ω)) ha
      simpa using this
    have h3 : (w k : Ω)⁻¹ = ∑ i, (a i : Ω) * ((w i : Ω) / (w k : Ω)) := by
      simp only [← mul_div_assoc, ← Finset.sum_div, h2, one_div]
    rw [h3]
    exact R'.sum_mem fun i _ => R'.mul_mem (h (a i).2) (hrat i)
  letI : Algebra R R' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K R R' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have halg : ∀ x : R, ((algebraMap R R' x : R') : Ω) = x := fun x => rfl
  have hsurj : ∀ z : Ω, z ∈ R' → ∃ (n : ℕ) (a : R), z * (w k : Ω) ^ n = a := by
    intro z hz
    rw [hR'] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact ⟨0, ⟨x, hx⟩, by simp⟩
      · exact ⟨1, w i, by field_simp⟩
    | algebraMap r => exact ⟨0, algebraMap K R r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * w k ^ n' + b * w k ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  haveI hloc : IsLocalization.Away (w k) R' := by
    refine IsLocalization.Away.mk (w k) ?_ ?_ ?_
    · refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
      apply Subtype.ext
      simp [halg, hk]
    · intro s
      obtain ⟨n, a, ha⟩ := hsurj s s.2
      refine ⟨n, a, Subtype.ext ?_⟩
      simpa [halg] using ha
    · intro a b hab
      refine ⟨0, ?_⟩
      have : (a : Ω) = b := by rw [← halg a, ← halg b, hab]
      rw [Subtype.ext this]
  refine ⟨h, hinv, fun hs => ?_, fun L _ _ ψ hψ => ?_⟩
  · haveI : Algebra.Smooth R R' := Algebra.Smooth.of_isLocalization_Away (w k)
    exact Algebra.Smooth.comp K R R'
  · have hu : IsUnit ((ψ : R →+* L) (w k)) := isUnit_iff_ne_zero.2 hψ
    let φ : R' →+* L := IsLocalization.Away.lift (w k) hu
    have hφ : ∀ x : R, φ (algebraMap R R' x) = ψ x := fun x =>
      IsLocalization.Away.lift_eq (w k) hu x
    refine ⟨{ φ with commutes' := fun r => ?_ }, ?_, fun i hi => ?_⟩
    · change φ (algebraMap K R' r) = _
      rw [IsScalarTower.algebraMap_apply K R R', hφ, AlgHom.commutes]
    · ext x; exact hφ x
    · change φ ⟨_, hi⟩ = _
      rw [eq_div_iff hψ, ← hφ, ← hφ, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [halg, hk]

end GlobalTheory
end
