module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableHolomorphicFamiliesSmooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox

@[expose] public section

section

open Topology Filter

theorem _root_.GlobalTheory.T.exists_countable_holomorphic_families_smooth : ∀ (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ), ∃ (ι : Type) (_ : Countable ι) (m : ι → ℕ) (B : ∀ i, Set (Fin (m i) → ℂ)) (φ : ∀ i, (Fin (m i) → ℂ) → (A →+* ℂ)), (∀ i, IsOpen (B i)) ∧ (∀ i, ∀ b ∈ B i, (φ i b).comp (algebraMap K A) = σ) ∧ (∀ i (a : A), DifferentiableOn ℂ (fun b => φ i b a) (B i)) ∧ (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → ∃ i, ∃ b ∈ B i, φ i b = ψ) ∧ ∀ i, ∀ b ∈ B i, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ i b' a ≠ 0 := by
  first | exact @GlobalTheory.SmoothPointCover.exists_countable_families | exact GlobalTheory.SmoothPointCover.exists_countable_families | (intros; apply GlobalTheory.SmoothPointCover.exists_countable_families <;> assumption)
end

section

namespace GlobalTheory

private theorem isFractionRing_of_closure_subset_range {Ω S : Type*} [Field Ω] [CommRing S]
    [Algebra S Ω] {t : Set Ω} (ht : Subfield.closure t = ⊤)
    (hinj : Function.Injective (algebraMap S Ω)) (hS : t ⊆ Set.range (algebraMap S Ω)) :
    IsFractionRing S Ω := by
  have : FaithfulSMul S Ω := (faithfulSMul_iff_algebraMap_injective S Ω).mpr hinj
  refine IsFractionRing.of_field S Ω fun z => ?_
  have hz : z ∈ Subfield.closure t := by rw [ht]; exact Subfield.mem_top z
  obtain ⟨y, hy, w, hw, rfl⟩ := Subfield.mem_closure_iff.mp hz
  have hsub : Subring.closure t ≤ (algebraMap S Ω).range :=
    Subring.closure_le.mpr (by rw [RingHom.coe_range]; exact hS)
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp (hsub hy)
  obtain ⟨b, rfl⟩ := RingHom.mem_range.mp (hsub hw)
  exact ⟨a, b, rfl⟩

theorem isFractionRing_subring_of_closure_eq_top {Ω : Type*} [Field Ω] {t : Set Ω}
    (ht : Subfield.closure t = ⊤) (D : Subring Ω) (hD : t ⊆ D) : IsFractionRing D Ω :=
  by
    refine isFractionRing_of_closure_subset_range ht Subtype.val_injective fun x hx => ?_
    exact ⟨⟨x, hD hx⟩, rfl⟩

theorem exists_normalisation_adjoin_finset_dvr :
    ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ (s : Finset Ω), Subfield.closure (Set.range (algebraMap O Ω) ∪ (s : Set Ω)) = ⊤ → ∃ A : Subalgebra O Ω, (s : Set Ω) ⊆ A ∧ Algebra.FiniteType O A ∧ Module.Flat O A ∧ IsIntegrallyClosed A ∧ IsFractionRing A Ω ∧ (∀ D : Subring Ω, IsIntegrallyClosed D → (∀ a, algebraMap O Ω a ∈ D) → (s : Set Ω) ⊆ D → (A : Set Ω) ⊆ D) ∧ ∀ (L : Type) [Field L] (W : ValuationSubring L) (φ : A →+* L), (∀ a, φ (algebraMap O A a) ∈ W) → (∀ (x : A), (x : Ω) ∈ s → φ x ∈ W) → ∀ x, φ x ∈ W := by
  intro O Ω _ _ _ _ _ _ hinj s hs
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap hinj
  set R : Subalgebra O Ω := Algebra.adjoin O (s : Set Ω) with hRdef
  have hsR : (s : Set Ω) ⊆ R := Algebra.subset_adjoin
  have hOR : ∀ a, algebraMap O Ω a ∈ R := fun a => R.algebraMap_mem a
  have htR : Set.range (algebraMap O Ω) ∪ (s : Set Ω) ⊆ Set.range (algebraMap R Ω) := by
    rintro x (⟨a, rfl⟩ | hx)
    · exact ⟨⟨_, hOR a⟩, rfl⟩
    · exact ⟨⟨x, hsR hx⟩, rfl⟩
  have : IsFractionRing R Ω := isFractionRing_of_closure_subset_range hs Subtype.val_injective htR
  have : Algebra.FiniteType O R := (Subalgebra.fg_iff_finiteType R).mp (Subalgebra.fg_adjoin_finset s)
  have : Algebra.EssFiniteType R Ω := Algebra.EssFiniteType.of_isLocalization Ω (nonZeroDivisors R)
  have hfin : Module.Finite R (integralClosure R Ω) :=
    finite_integralClosure_of_essFiniteType_field (o := O) (R := R) Ω
  set B : Subalgebra R Ω := integralClosure R Ω with hBdef
  have hRB : ∀ x, x ∈ R → x ∈ B := fun x hx => B.algebraMap_mem ⟨x, hx⟩
  have htB : Set.range (algebraMap O Ω) ∪ (s : Set Ω) ⊆ Set.range (algebraMap B Ω) := by
    rintro x (⟨a, rfl⟩ | hx)
    · exact ⟨⟨_, hRB _ (hOR a)⟩, rfl⟩
    · exact ⟨⟨x, hRB _ (hsR hx)⟩, rfl⟩
  have hBfrac : IsFractionRing B Ω := isFractionRing_of_closure_subset_range hs Subtype.val_injective htB
  have hBic : IsIntegrallyClosed B := by
    refine (isIntegrallyClosed_iff Ω).mpr fun {x} hx => ?_
    have hx' : x ∈ integralClosure B Ω := hx
    rw [hBdef, integralClosure_idem] at hx'
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp hx'
    exact ⟨y, rfl⟩
  have hkey : ∀ (L : Type) [Field L] (W : ValuationSubring L) (φ : B →+* L),
      (∀ y (hy : y ∈ R), φ (algebraMap R B ⟨y, hy⟩) ∈ W) → ∀ x, φ x ∈ W := by
    intro L _ W φ hφ x
    let φR : R →+* W := (φ.comp (algebraMap R B)).codRestrict W.toSubring fun r => hφ r.1 r.2
    have hx : IsIntegral W (φ x) :=
      IsIntegral.map_of_comp_eq φR φ (by ext r; rfl) (Algebra.IsIntegral.isIntegral x)
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).mp inferInstance hx
    rw [← hy]
    exact y.2
  refine ⟨B.restrictScalars O, fun x hx => hRB x (hsR hx), ?_, ?_, ?_, hBfrac, ?_, ?_⟩
  · have hBO : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
    exact hBO
  · have : Module.IsTorsionFree O (B.restrictScalars O) := by
      refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
      have h' := congrArg Subtype.val h
      rw [Subalgebra.coe_smul, Algebra.smul_def, ZeroMemClass.coe_zero, mul_eq_zero] at h'
      rcases h' with h' | h'
      · exact Or.inl (hinj (by rw [h', map_zero]))
      · exact Or.inr (Subtype.ext h')
    infer_instance
  · exact hBic
  · intro D hDic hDO hDs x hx
    have hRD : R.toSubring ≤ D := by
      rw [hRdef, Algebra.adjoin_eq_ring_closure]
      exact Subring.closure_le.mpr (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact hDO a) hDs)
    have : IsFractionRing D Ω := isFractionRing_subring_of_closure_eq_top hs D
      (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact hDO a) hDs)
    have hxi : IsIntegral R x := hx
    have hxD : IsIntegral D x :=
      IsIntegral.map_of_comp_eq (Subring.inclusion hRD : R →+* D) (RingHom.id Ω) (by ext r; rfl) hxi
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff Ω).mp hDic hxD
    rw [← hy]
    exact y.2
  · intro L _ W φ hO hs' x
    let ψ : B →+* L := φ
    refine hkey L W ψ (fun y hy => ?_) x
    induction hy using Algebra.adjoin_induction with
    | mem z hz => exact hs' ⟨z, hRB z (hsR hz)⟩ hz
    | algebraMap a => exact hO a
    | add y z hy hz ihy ihz =>
      have e : (⟨y + z, add_mem hy hz⟩ : R) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e, map_add (f := _), RingHom.map_add ψ]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, mul_mem hy hz⟩ : R) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [e, map_mul, RingHom.map_mul ψ]
      exact mul_mem ihy ihz

end GlobalTheory
end

section

namespace GlobalTheory.WeakApprox

theorem exists_integral_congr (Ω : Type) [Field Ω] (ι : Type) [Finite ι]
    (v : ι → Valuation Ω (WithZero (Multiplicative ℤ)))
    (hgen : ∀ i, ∃ x, v i x =
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hind : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) (i₀ : ι) (a : Ω) (ha : v i₀ a ≤ 1) :
    ∃ a' : Ω, (∀ i, v i a' ≤ 1) ∧ v i₀ (a - a') < 1 := by
  classical
  haveI := Fintype.ofFinite ι

  have hn : ∀ i, ∃ n : ℤ, 1 ≤ n ∧
      v i a ≤ ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro i
    rcases eq_or_ne (v i a) 0 with h | h
    · exact ⟨1, le_rfl, by simp [h]⟩
    · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp h
      refine ⟨max 1 (Multiplicative.toAdd m), le_max_left _ _, ?_⟩
      rw [← hm, WithZero.coe_le_coe]
      exact le_max_right (1 : ℤ) (Multiplicative.toAdd m)
  choose n hn1 hn2 using hn

  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq v hgen hind
    (fun i => if i = i₀ then -1 else n i)
  have ht0 : v i₀ t < 1 := by
    rw [ht i₀, if_pos rfl, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    norm_num
  have h1t : v i₀ (1 + t) = 1 := by
    rw [(v i₀).map_add_eq_of_lt_left (by rwa [(v i₀).map_one]), (v i₀).map_one]
  have hne : 1 + t ≠ 0 := by
    intro h0
    rw [h0, (v i₀).map_zero] at h1t
    exact zero_ne_one h1t
  refine ⟨a / (1 + t), fun i => ?_, ?_⟩
  · rw [map_div₀]
    by_cases hi : i = i₀
    · subst hi
      rw [h1t, div_one]
      exact ha
    · have hti : v i t = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
        rw [ht i, if_neg hi]
      have hlt : v i 1 < v i t := by
        rw [hti, (v i).map_one, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
          Multiplicative.ofAdd_lt]
        linarith [hn1 i]
      rw [(v i).map_add_eq_of_lt_right hlt, hti]
      exact div_le_one_of_le₀ (hn2 i) zero_le'
  · have hsub : a - a / (1 + t) = a * t / (1 + t) := by
      field_simp
      ring
    rw [hsub, map_div₀, h1t, div_one, map_mul]
    calc v i₀ a * v i₀ t ≤ 1 * v i₀ t := by gcongr
      _ = v i₀ t := one_mul _
      _ < 1 := ht0

end GlobalTheory.WeakApprox
end
