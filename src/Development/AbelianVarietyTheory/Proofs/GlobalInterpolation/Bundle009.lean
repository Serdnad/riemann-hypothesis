module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

section

namespace GlobalTheory.PowerSeriesIdealPowers

open MvPowerSeries IsLocalRing

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ maximalIdeal (MvPowerSeries σ O) ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

theorem mem_smul_top_iff {S : Type} [CommRing S] (I : Ideal S) (x : S) :
    x ∈ (I • ⊤ : Submodule S S) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem coeff_mem_of_mem_pow {σ : Type} (n : ℕ) :
    ∀ f ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n, ∀ d : σ →₀ ℕ,
      coeff d f ∈ (maximalIdeal O) ^ (n - d.degree) := by
  classical
  induction n with
  | zero => intro f _ d; simp
  | succ n ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy d
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 := ih x hx p.1
      have h2 : coeff p.2 y ∈ (maximalIdeal O) ^ (1 - p.2.degree) := by
        by_cases h0 : p.2.degree = 0
        · rw [Finsupp.degree_eq_zero_iff] at h0
          rw [h0, coeff_zero_eq_constantCoeff_apply]
          simpa using (mem_max_iff y).1 hy
        · rw [show 1 - p.2.degree = 0 by omega]; simp
      have hdeg : d.degree = p.1.degree + p.2.degree := by rw [← hp, map_add (f := _)]
      have hle : n + 1 - d.degree ≤ (n - p.1.degree) + (1 - p.2.degree) := by omega
      exact Ideal.pow_le_pow_right hle (by rw [pow_add]; exact Ideal.mul_mem_mul h1 h2)
    · intro x y hx hy d
      rw [map_add (f := coeff d)]; exact add_mem (hx d) (hy d)

theorem coeff_X_mul_add {σ : Type} [DecidableEq σ] (i : σ) (g : MvPowerSeries σ O) (d : σ →₀ ℕ) :
    coeff (d + Finsupp.single i 1) (X i * g) = coeff d g := by
  rw [X, coeff_monomial_mul]
  simp

theorem C_mem_pow {σ : Type} (n : ℕ) (c : O) (hc : c ∈ (maximalIdeal O) ^ n) :
    C c ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n := by
  have h1 : C c ∈ Ideal.map (C (σ := σ)) ((maximalIdeal O) ^ n) := Ideal.mem_map_of_mem _ hc
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ n h1
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_max_iff, constantCoeff_C]
  exact hx

theorem X_mem_max {σ : Type} (i : σ) : (X i : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := by
  rw [mem_max_iff, constantCoeff_X]; exact zero_mem _

theorem mem_pow_of_coeff_mem (a n : ℕ) :
    ∀ f : MvPowerSeries (Fin a) O, (∀ d : Fin a →₀ ℕ, coeff d f ∈ (maximalIdeal O) ^ (n - d.degree)) →
      f ∈ (maximalIdeal (MvPowerSeries (Fin a) O)) ^ n := by
  classical
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    let P : Fin a → (Fin a →₀ ℕ) → Prop := fun i d => d i ≠ 0 ∧ ∀ j < i, d j = 0
    let fi : Fin a → MvPowerSeries (Fin a) O := fun i d => if P i d then coeff d f else 0
    have hfi : ∀ i d, coeff d (fi i) = if P i d then coeff d f else 0 := fun i d => rfl
    have huniq : ∀ i j d, P i d → P j d → i = j := by
      intro i j d hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact absurd (hj.2 i h) hi.1
      · exact h
      · exact absurd (hi.2 j h) hj.1
    have hexists : ∀ d : Fin a →₀ ℕ, d ≠ 0 → ∃ i, P i d := by
      intro d hd
      have hs : d.support.Nonempty := Finsupp.support_nonempty_iff.2 hd
      refine ⟨d.support.min' hs, Finsupp.mem_support_iff.1 (Finset.min'_mem _ hs), fun j hj => ?_⟩
      by_contra hne
      exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.2 hne)) (not_le.2 hj)
    have hdecomp : f = C (constantCoeff f) + ∑ i, fi i := by
      ext d

      rw [map_add (f := _), map_sum, coeff_C]
      simp only [hfi]
      by_cases hd : d = 0
      · subst hd
        have : ∀ i, ¬ P i 0 := fun i h => h.1 rfl
        simp [this, coeff_zero_eq_constantCoeff_apply]
      · obtain ⟨i, hi⟩ := hexists d hd
        rw [if_neg hd, zero_add, Finset.sum_eq_single i (fun j _ hj => by
          rw [if_neg (fun h => hj (huniq _ _ _ h hi))]) (fun h => absurd (Finset.mem_univ i) h),
          if_pos hi]
    rw [hdecomp]
    refine add_mem (C_mem_pow _ _ ?_) (Ideal.sum_mem _ fun i _ => ?_)
    · simpa [coeff_zero_eq_constantCoeff_apply] using hf 0
    · have hdvd : (X i : MvPowerSeries (Fin a) O) ∣ fi i := by
        rw [X_dvd_iff]
        intro m hm
        rw [hfi, if_neg (fun h => h.1 hm)]
      obtain ⟨g, hg⟩ := hdvd
      rw [hg, pow_succ']
      refine Ideal.mul_mem_mul (X_mem_max i) (ih g fun d => ?_)
      rw [← coeff_X_mul_add i g d, ← hg, hfi]
      split_ifs
      · have := hf (d + Finsupp.single i 1)
        rwa [map_add, Finsupp.degree_single, show n + 1 - (d.degree + 1) = n - d.degree by omega] at this
      · exact zero_mem _

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    [IsPrecomplete (IsLocalRing.maximalIdeal O) O] (a : ℕ),
    IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) := by
  intro O _ _ hO a
  constructor
  intro f hf
  simp only [SModEq.sub_mem, mem_smul_top_iff] at hf ⊢
  let s : (Fin a →₀ ℕ) → ℕ → O := fun d k => coeff d (f (k + d.degree))
  have hs : ∀ d, ∃ L : O, ∀ k, s d k ≡ L [SMOD ((maximalIdeal O) ^ k • ⊤ : Submodule O O)] := by
    intro d
    refine IsPrecomplete.prec hO ?_
    intro k l hkl
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have h := coeff_mem_of_mem_pow (k + d.degree) _ (hf (Nat.add_le_add_right hkl _)) d
    rwa [map_sub, Nat.add_sub_cancel] at h
  choose L hL using hs
  let Lim : MvPowerSeries (Fin a) O := fun d => L d
  have hLim : ∀ d, coeff d Lim = L d := fun d => rfl
  refine ⟨Lim, fun n => mem_pow_of_coeff_mem a n _ fun d => ?_⟩
  rw [map_sub, hLim]
  by_cases hd : d.degree ≤ n
  · have h := hL d (n - d.degree)
    rw [SModEq.sub_mem, mem_smul_top_iff] at h
    simp only [s, Nat.sub_add_cancel hd] at h
    exact h
  · rw [show n - d.degree = 0 by omega]; simp
end GlobalTheory.PowerSeriesIdealPowers
end

section

open IsLocalRing Matrix

namespace GlobalTheory.RegularQuotient


open IsLocalRing Matrix in
theorem _root_.GlobalTheory.RegularQuotient.quot_regular (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι κ : Type} [Fintype ι]
    [Fintype κ] (t : ι → Λ) (z : κ → Λ)
    (hs : Ideal.span (Set.range t ∪ Set.range z) = maximalIdeal Λ)
    (hd : ringKrullDim Λ = ((Fintype.card ι + Fintype.card κ : ℕ) : ℕ)) :
    ∃ _ : IsRegularLocalRing (Λ ⧸ Ideal.span (Set.range z)),
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range z))) (maximalIdeal Λ) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range z)) (t i)) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      ringKrullDim (Λ ⧸ Ideal.span (Set.range z)) = (Fintype.card ι : ℕ) := by
  set I := Ideal.span (Set.range z) with hIdef
  have hIm : I ≤ maximalIdeal Λ := by
    rw [Ideal.span_le, ← hs]
    exact (Set.subset_union_right).trans Ideal.subset_span
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal Λ).ne_top hIm
  haveI : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (Λ ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal Λ) = maximalIdeal (Λ ⧸ I) := by
    have hc : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (Λ ⧸ I)) = maximalIdeal Λ :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (t i)) =
      maximalIdeal (Λ ⧸ I) := by
    rw [← hmap, ← hs, Ideal.span_union, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hgen : ((maximalIdeal (Λ ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (Fintype.card ι : ℕ) := by
    rw [← hspan]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (t i))
    have h' : (Set.range fun i => Ideal.Quotient.mk I (t i)).ncard ≤ Fintype.card ι := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hle : ringKrullDim (Λ ⧸ I) ≤ (Fintype.card ι : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans hgen
  have hI : (I.spanFinrank : WithBot ℕ∞) ≤ (Fintype.card κ : ℕ) := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ) (Set.finite_range z)
    have h' : (Set.range z).ncard ≤ Fintype.card κ := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hge := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
    (by rw [ringJacobson_eq_maximalIdeal]; exact hIm)
  rw [hd] at hge
  have h1 : ((Fintype.card ι + Fintype.card κ : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (Λ ⧸ I) + (Fintype.card κ : ℕ) :=
    hge.trans (add_le_add le_rfl hI)
  have hdim : ringKrullDim (Λ ⧸ I) = (Fintype.card ι : ℕ) := by
    generalize ringKrullDim (Λ ⧸ I) = e at h1 hle ⊢
    induction e using WithBot.recBotCoe with
    | bot => simp at h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (by exact_mod_cast (not_le.mpr (ENat.coe_lt_top _)))
      | coe n =>
        norm_cast at h1 hle ⊢
        omega
  exact ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hgen.trans hdim.ge), hmap, hspan,
    hdim⟩


open IsLocalRing Matrix in
theorem _root_.GlobalTheory.RegularQuotient.exists_extend (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι : Type} [Fintype ι]
    (τ : ι → maximalIdeal Λ)
    (hτ : LinearIndependent (ResidueField Λ) (fun i => (maximalIdeal Λ).toCotangent (τ i))) :
    ∃ (J : Type) (_ : Fintype J) (t : J → Λ),
      Ideal.span (Set.range t ∪ Set.range fun i => (τ i : Λ)) = maximalIdeal Λ ∧
      ringKrullDim Λ = ((Fintype.card J + Fintype.card ι : ℕ) : ℕ) := by
  set N : Submodule (ResidueField Λ) (CotangentSpace Λ) :=
    Submodule.span (ResidueField Λ) (Set.range fun i => (maximalIdeal Λ).toCotangent (τ i))
    with hN
  let b := Module.finBasis (ResidueField Λ) (CotangentSpace Λ ⧸ N)
  have hsurj : Function.Surjective
      fun y : maximalIdeal Λ => N.mkQ ((maximalIdeal Λ).toCotangent y) :=
    (Submodule.mkQ_surjective N).comp (maximalIdeal Λ).toCotangent_surjective
  choose s hs using fun j => hsurj (b j)
  refine ⟨Fin (Module.finrank (ResidueField Λ) (CotangentSpace Λ ⧸ N)), inferInstance,
    fun j => (s j : Λ), ?_, ?_⟩
  · have htop : Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ)) = ⊤ := by
      set P := Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ))
      have hNP : N ≤ P := by
        rw [hN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨τ i, Or.inr ⟨i, rfl⟩, rfl⟩
      have hmap : Submodule.map N.mkQ P = ⊤ := by
        rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨_, Submodule.subset_span ⟨s j, Or.inl ⟨j, rfl⟩, rfl⟩, hs j⟩
      rw [Submodule.map_mkQ_eq_top, sup_eq_right.mpr hNP] at hmap
      exact hmap
    rw [IsLocalRing.CotangentSpace.span_image_eq_top_iff] at htop
    have key := congrArg (Submodule.map (maximalIdeal Λ).subtype) htop
    rw [← Submodule.span_image, Submodule.map_subtype_top, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at key
    exact key
  · rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace Λ).mp inferInstance, Fintype.card_fin,
      ← finrank_span_eq_card hτ, ← hN, Submodule.finrank_quotient_add_finrank]

open IsLocalRing Matrix in
private theorem linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq (A : Type) [CommRing A]
    [IsRegularLocalRing A] (k : ℕ) (x : Fin k → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hind : ∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
      (fun i => (maximalIdeal A).toCotangent (⟨x i, hx i⟩ : maximalIdeal A)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => IsLocalRing.residue_surjective (g j)
  have hmem : (∑ j, a j * x j) ∈ maximalIdeal A :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j)
  have hsum : (∑ j, a j * x j) ∈ maximalIdeal A ^ 2 := by
    rw [← Ideal.toCotangent_eq_zero (maximalIdeal A) ⟨_, hmem⟩]
    have he : (⟨∑ j, a j * x j, hmem⟩ : maximalIdeal A) =
        ∑ j, a j • (⟨x j, hx j⟩ : maximalIdeal A) := by
      ext; simp [Submodule.coe_sum, smul_eq_mul]

    rw [he, map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← ha j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  rw [← ha i, IsLocalRing.residue_eq_zero_iff]
  exact hind a hsum i


open IsLocalRing Matrix in
theorem _root_.GlobalTheory.RegularQuotient.quotient_span_range : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d k : ℕ)
    (x : Fin k → A),
    ringKrullDim A = ((d + k : ℕ) : WithBot ℕ∞) → (∀ i, x i ∈ maximalIdeal A) →
    (∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) →
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (A ⧸ Ideal.span (Set.range x)) = (d : WithBot ℕ∞) := by
  intro A _ _ d k x hd hx hind
  obtain ⟨J, _, t, hspan, hdim⟩ := _root_.GlobalTheory.RegularQuotient.exists_extend A
    (fun i => (⟨x i, hx i⟩ : maximalIdeal A))
    (linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq A k x hx hind)
  have hJ : Fintype.card J = d := by
    rw [hd, Fintype.card_fin] at hdim
    have h : d + k = Fintype.card J + k := by exact_mod_cast hdim
    omega
  have hspan' : Ideal.span (Set.range t ∪ Set.range x) = maximalIdeal A := hspan
  have hdim' : ringKrullDim A = ((Fintype.card J + Fintype.card (Fin k) : ℕ) : ℕ) := by
    rw [hd, Fintype.card_fin, hJ]
  obtain ⟨hreg, -, -, hq⟩ := _root_.GlobalTheory.RegularQuotient.quot_regular A t x hspan' hdim'
  exact ⟨hreg, by rw [hq, hJ]⟩

end GlobalTheory.RegularQuotient
end
