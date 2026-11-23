module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.GroupTheory.Coset.Card

@[expose] public section

section

namespace GlobalTheory

open PowerSeries

theorem free_of_X_regular_quotient_torsionFree_scalarTower (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M] [Module O M] [IsScalarTower O (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  classical
  set p : Submodule (PowerSeries O) M :=
    Ideal.span {(PowerSeries.X : PowerSeries O)} • (⊤ : Submodule (PowerSeries O) M) with hp
  have memp : ∀ m : M, m ∈ p ↔ ∃ y : M, m = (PowerSeries.X : PowerSeries O) • y := by
    intro m
    rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Submodule.mem_top, hy.symm⟩
  have hsmul : ∀ (c : O) (m : M), c • m = (PowerSeries.C c : PowerSeries O) • m := by
    intro c m
    rw [← IsScalarTower.algebraMap_smul (PowerSeries O) c m, PowerSeries.algebraMap_apply]
    simp

  have hdec : ∀ r : PowerSeries O, ∃ s : PowerSeries O,
      r = PowerSeries.C (PowerSeries.constantCoeff r) + PowerSeries.X * s := by
    intro r
    obtain ⟨s, hs⟩ : (PowerSeries.X : PowerSeries O) ∣
        r - PowerSeries.C (PowerSeries.constantCoeff r) := by
      rw [PowerSeries.X_dvd_iff]
      simp
    exact ⟨s, by rw [← hs]; ring⟩

  have hN : ∀ (r : PowerSeries O) (y : M ⧸ p), r • y = (PowerSeries.constantCoeff r) • y := by
    intro r y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    obtain ⟨s, hs⟩ := hdec r
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, memp]
    have e1 : r • m = (PowerSeries.C (PowerSeries.constantCoeff r) : PowerSeries O) • m
        + (PowerSeries.X : PowerSeries O) • (s • m) := by
      conv_lhs => rw [hs]
      rw [add_smul, mul_smul]
    refine ⟨s • m, ?_⟩
    rw [e1, hsmul]
    abel
  have hfin : Module.Finite O (M ⧸ p) := by
    obtain ⟨T, hT'⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (PowerSeries O) (M ⧸ p))
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    rintro y -
    have hy : y ∈ Submodule.span (PowerSeries O) (T : Set (M ⧸ p)) := by
      rw [hT']
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [hN]
      exact Submodule.smul_mem _ _ hx
  have htf : Module.IsTorsionFree O (M ⧸ p) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c y hcy => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, memp, hsmul c m] at hcy
      rw [Submodule.Quotient.mk_eq_zero, memp]
      exact hT c m hc hcy
  let b := Module.Free.chooseBasis O (M ⧸ p)
  choose e he using fun i => Submodule.Quotient.mk_surjective p (b i)
  have hspan : (⊤ : Submodule (PowerSeries O) M) ≤ Submodule.span (PowerSeries O) (Set.range e) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {PowerSeries.X})
      (Module.finite_def.mp inferInstance) ?_ ?_
    · rw [Ideal.span_le]
      rintro _ rfl
      change PowerSeries.X ∈ Ideal.jacobson (⊥ : Ideal (PowerSeries O))
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp
    · intro m _
      set c := b.repr (Submodule.Quotient.mk m)
      have h2 : m - ∑ i, c i • e i ∈ p := by

        rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply p (∑ i, c i • e i), map_sum]
        simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, he]
        exact (b.sum_repr _).symm
      rw [Submodule.mem_sup]
      refine ⟨∑ i, c i • e i, ?_, m - ∑ i, c i • e i, h2, by abel⟩
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (PowerSeries O) e := by
    rw [Fintype.linearIndependent_iff]

    have key : ∀ k : ℕ, ∀ g : Module.Free.ChooseBasisIndex O (M ⧸ p) → PowerSeries O,
        ∑ i, g i • e i = 0 → ∀ i, (PowerSeries.X : PowerSeries O) ^ k ∣ g i := by
      intro k
      induction k with
      | zero =>
        intro g _ i
        simp
      | succ k ih =>
        intro g hg i
        choose s hs using fun j => hdec (g j)
        have hc : ∀ j, PowerSeries.constantCoeff (g j) = 0 := by
          have h0 : ∑ j, (PowerSeries.constantCoeff (g j)) • b j = 0 := by
            have h1 := congrArg p.mkQ hg

            simp only [map_sum, map_smul, Submodule.mkQ_apply, he, hN, map_zero] at h1
            exact h1
          exact (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0
        have hgX : ∀ j, g j = PowerSeries.X * s j := by
          intro j
          rw [hs j, hc j]
          simp
        have hg' : (PowerSeries.X : PowerSeries O) • ∑ j, s j • e j = 0 := by
          rw [Finset.smul_sum, ← hg]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hgX j, mul_smul]
        obtain ⟨t, ht⟩ := ih s (hX _ hg') i
        exact ⟨t, by rw [hgX i, ht]; ring⟩
    intro g hg i
    ext n
    have h := PowerSeries.X_pow_dvd_iff.mp (key (n + 1) g hg i) n (Nat.lt_succ_self n)
    simpa using h
  exact Module.Free.of_basis (Module.Basis.mk hli hspan)

theorem free_of_X_regular_of_quotient_torsionFree (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  let _ : Module O M := Module.compHom M (algebraMap O (PowerSeries O))
  have : IsScalarTower O (PowerSeries O) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact free_of_X_regular_quotient_torsionFree_scalarTower O M hX hT

end GlobalTheory
end

section

namespace GlobalTheory.SaturatedComplement

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) (h : ∀ (a : O) (x : M), a ≠ (0 : O) → a • x ∈ N → x ∈ N) :
    ∃ C : Submodule O M, IsCompl N C := by
  have htf : Module.IsTorsionFree O (M ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact h a x ha hq
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hsec : ∀ q, N.mkQ (s q) = q := fun q => by
    simpa using LinearMap.congr_fun hs q
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxN ⟨q, rfl⟩
    have hq : q = 0 := by
      rw [← hsec q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxN
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply, hsec, sub_self]
    have := Submodule.add_mem_sup hx (LinearMap.mem_range_self s (N.mkQ x))
    simpa using this

end GlobalTheory.SaturatedComplement
end

section

namespace GlobalTheory

theorem finite_sq_eq_one_of_finite_algebra (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A]
    [Algebra k A] [Module.Finite k A] : Set.Finite {x : A | x ^ 2 = 1} := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Finite (TopologicalSpace.Clopens (PrimeSpectrum A)) :=
    Finite.of_injective (fun s : TopologicalSpace.Clopens (PrimeSpectrum A) => (s : Set (PrimeSpectrum A)))
      SetLike.coe_injective
  haveI : Finite {e : A // IsIdempotentElem e} :=
    Finite.of_equiv _ (PrimeSpectrum.isIdempotentElemEquivClopens (R := A)).symm.toEquiv
  set c : A := algebraMap k A (2⁻¹ : k) with hc
  have hc2 : c * 2 = 1 := by
    rw [hc, (map_ofNat (algebraMap k A) 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : k) ≠ 0), map_one]
  have hmap : ∀ x : A, x ^ 2 = 1 → IsIdempotentElem (c * (1 + x)) := by
    intro x hx
    unfold IsIdempotentElem
    have : (c * (1 + x)) * (c * (1 + x)) = c * (c * 2) * (1 + x) := by
      linear_combination (c * c) * hx
    rw [this, hc2, mul_one]
  have hinj : Set.InjOn (fun x : A => c * (1 + x)) {x : A | x ^ 2 = 1} := by
    intro x _ y _ hxy
    have h : (2 : A) * (c * (1 + x)) = 2 * (c * (1 + y)) := by simp only at hxy; rw [hxy]
    have e : ∀ z : A, (2 : A) * (c * (1 + z)) = 1 + z := fun z => by
      rw [← mul_assoc, mul_comm (2 : A) c, hc2, one_mul]
    rw [e, e] at h
    exact add_left_cancel h
  have hfin : Set.Finite {e : A | IsIdempotentElem e} :=
    Set.finite_coe_iff.mp (‹Finite {e : A // IsIdempotentElem e}› :)
  exact Set.Finite.of_finite_image (hfin.subset (by
    rintro _ ⟨x, hx, rfl⟩; exact hmap x hx)) hinj

end GlobalTheory
end

section

namespace GlobalTheory

theorem finite_jumps_inf_filtration (E W : Type) [Field E] [AddCommGroup W] [Module E W]
    (D : Submodule E W) (F : ℤ → Submodule E W) (hD : Module.Finite E ↥D)
    (hF : ∀ a, F (a + 1) ≤ F a) :
    {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  have hanti : Antitone F := antitone_int_of_succ_le hF
  have hfin : ∀ a, Module.Finite E ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := D) inf_le_left
  have key : ∀ a b : ℤ, D ⊓ F (a + 1) ≠ D ⊓ F a → a < b →
      Module.finrank E ↥(D ⊓ F b) < Module.finrank E ↥(D ⊓ F a) := by
    intro a b ha hab
    haveI := hfin a
    apply Submodule.finrank_lt_finrank_of_lt
    have h1 : D ⊓ F b ≤ D ⊓ F (a + 1) := inf_le_inf_left _ (hanti (by omega))
    have h2 : D ⊓ F (a + 1) < D ⊓ F a := lt_of_le_of_ne (inf_le_inf_left _ (hF a)) ha
    exact lt_of_le_of_lt h1 h2
  refine Set.Finite.of_injOn (f := fun a => Module.finrank E ↥(D ⊓ F a))
    (t := Set.Iic (Module.finrank E ↥D)) ?_ ?_ (Set.finite_Iic _)
  · intro a _
    exact Submodule.finrank_mono inf_le_left
  · intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (key a b ha h).ne'
    · exact h
    · exact absurd hab (key b a hb h).ne

end GlobalTheory
end

section

namespace GlobalTheory.PowerScalarMembership

theorem pow_smul_mem_of_le {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]
    (L : Submodule O V) (c : O) {x : V} {m n : ℕ} (hmn : m ≤ n) (h : c ^ m • x ∈ L) :
    c ^ n • x ∈ L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, mul_comm, mul_smul]
  exact L.smul_mem _ h

theorem exists_pow_smul_mem {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, c ^ m • x ∈ L := by
  have hx : x ∈ Submodule.span LL (L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨max m n, ?_⟩
    rw [smul_add]
    exact L.add_mem (pow_smul_mem_of_le L c (le_max_left _ _) hm)
      (pow_smul_mem_of_le L c (le_max_right _ _) hn)
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨k, b, hb⟩ := hc a
    refine ⟨k + m, ?_⟩
    have key : c ^ (k + m) • (a • y) = b • (c ^ m • y) := by
      rw [← algebraMap_smul LL (c ^ (k + m)), smul_smul, ← algebraMap_smul LL b,
        ← algebraMap_smul LL (c ^ m), smul_smul, hb, map_pow, map_pow, pow_add]
      congr 1
      ring
    rw [key]
    exact L.smul_mem b hm

theorem main : ∀ {LL O : Type} [inst : Field LL] [inst_1 : CommRing O] [inst_2 : Algebra O LL] [TopologicalSpace LL] {V : Type} [inst_4 : AddCommGroup V] [inst_5 : Module LL V] [inst_6 : Module O V] [IsScalarTower O LL V] (c : O), (∀ (a : LL), ∃ (k : ℕ) (b : O), (Algebra.algebraMap O LL : O → LL) b = (Algebra.algebraMap O LL : O → LL) c ^ k * a) → ∀ (L S : Submodule O V), Submodule.span LL (↑L : Set V) = ⊤ → Submodule.FG S → ∃ (m : ℕ), ∀ x ∈ S, c ^ m • x ∈ L := by
  intro LL O _ _ _ _ V _ _ _ _ c hc L S hL hS
  obtain ⟨s, rfl⟩ := hS
  choose f hf using fun x => exists_pow_smul_mem (LL := LL) c hc L hL x
  refine ⟨s.sup f, fun x hx => ?_⟩
  have hle : Submodule.span O (s : Set V) ≤ L.comap ((c ^ s.sup f) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    exact pow_smul_mem_of_le L c (Finset.le_sup hy) (hf y)
  simpa using hle hx

end GlobalTheory.PowerScalarMembership
end

section

namespace GlobalTheory.ClosedStatement

open Ideal Module

theorem main {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : Ideal.IsMaximal m] (hne : Ideal.map f m ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = (1 : A) ∧
      (∀ x : A, ∃ a : ι →₀ R, (x - Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i)
        ∈ Ideal.map f m) ∧
      ∀ a : ι →₀ R, (Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i) ∈ Ideal.map f m →
        ∀ i : ι, (a : ι → R) i ∈ m := by
  classical
  letI : Algebra R A := f.toAlgebra
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hf : algebraMap R A = f := rfl
  rw [← hf] at hne ⊢
  haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R A) m) := Ideal.Quotient.nontrivial_iff.mpr hne
  have hli : LinearIndepOn (R ⧸ m) id ({1} : Set (A ⧸ Ideal.map (algebraMap R A) m)) :=
    (linearIndepOn_singleton_iff (R ⧸ m)).mpr one_ne_zero
  let v := Basis.extend hli
  have h1mem : (1 : A ⧸ Ideal.map (algebraMap R A) m) ∈ hli.extend (Set.subset_univ _) :=
    Basis.subset_extend hli rfl
  let b : ↥(hli.extend (Set.subset_univ _)) → A := fun i =>
    if (i : A ⧸ Ideal.map (algebraMap R A) m) = 1 then 1
    else (Ideal.Quotient.mk_surjective (i : A ⧸ Ideal.map (algebraMap R A) m)).choose
  have hb : ∀ i, Ideal.Quotient.mk (Ideal.map (algebraMap R A) m) (b i) = v i := by
    intro i
    rw [Basis.coe_extend]
    simp only [b]
    split_ifs with h
    · rw [map_one, h]
    · exact (Ideal.Quotient.mk_surjective _).choose_spec
  have key : ∀ a : ↥(hli.extend (Set.subset_univ _)) →₀ R,
      Ideal.Quotient.mk (Ideal.map (algebraMap R A) m)
        (Finsupp.sum a fun i y ↦ (algebraMap R A) y * b i) =
      Finsupp.linearCombination (R ⧸ m) v (a.mapRange (Ideal.Quotient.mk m) (map_zero _)) := by
    intro a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    rw [map_mul, hb, Algebra.smul_def, Ideal.Quotient.algebraMap_quotient_map_quotient]
  refine ⟨_, b, ⟨1, h1mem⟩, by simp [b], ?_, ?_⟩
  · intro x
    let g : R ⧸ m → R := fun c => if c = 0 then 0 else (Ideal.Quotient.mk_surjective c).choose
    have hg : ∀ c, Ideal.Quotient.mk m (g c) = c := by
      intro c
      simp only [g]
      split_ifs with h
      · rw [h, map_zero]
      · exact (Ideal.Quotient.mk_surjective c).choose_spec
    refine ⟨(v.repr (Ideal.Quotient.mk _ x)).mapRange g (by simp [g]), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, key]
    have hc : ∀ c : ↥(hli.extend (Set.subset_univ _)) →₀ R ⧸ m,
        (c.mapRange g (by simp [g])).mapRange (Ideal.Quotient.mk m) (map_zero _) = c := by
      intro c; ext i; simp [hg]
    rw [hc, Basis.linearCombination_repr, sub_self]
  · intro a ha i
    rw [← Ideal.Quotient.eq_zero_iff_mem, key] at ha
    have h0 := linearIndependent_iff.mp v.linearIndependent _ ha
    have := congrArg (fun l => l i) h0
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this

end GlobalTheory.ClosedStatement
end

section

namespace GlobalTheory

private lemma card_eq_card_residueField_of_isSimpleModule' (O : Type) [CommRing O]
    [IsLocalRing O] (S : Type) [AddCommGroup S] [Module O S] [IsSimpleModule O S] :
    Nat.card S = Nat.card (IsLocalRing.ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := O) (M := S)).mp ‹_›
  have hI' : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hI'
  exact Nat.card_congr e.toEquiv

theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨0, ?_, ?_⟩
    · simpa using (Module.length_eq_zero_iff (R := O) (M := M)).mpr ‹_›
    · simp [Nat.card_of_subsingleton (0 : M)]
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hl, hc⟩ := ih
    refine ⟨n + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hl, Module.length_eq_one_iff.mpr ‹_›]
      push_cast
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [card_eq_card_residueField_of_isSimpleModule' O (M ⧸ N), hc, pow_succ, mul_comm]

theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Finite M] :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end GlobalTheory
end
