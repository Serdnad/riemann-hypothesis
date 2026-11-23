module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
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
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.V.FW

private theorem UpperTheory.V.FW.phiDvd_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (k A : Type) [Field k] [CharP k l]
    [CommRing A] [Algebra k A] (x : A) : (x - 1) ^ l ^ n = x ^ l ^ n - 1 := by
  have h : ((Polynomial.X : Polynomial k) - 1) ^ l ^ n = Polynomial.X ^ l ^ n - 1 := by
    rw [sub_pow_char_pow, one_pow]
  have := congrArg (Polynomial.aeval x) h
  simpa using this

private theorem UpperTheory.V.FW.phiDvd_nil (k A : Type) [Field k] [CommRing A] [Algebra k A] (T φ : A)
    (hT : IsNilpotent T) (hφ : φ ∈ Algebra.adjoin k {T}) (N : ℕ) (h : ¬ T ^ N ∣ φ) : φ ∣ T ^ N := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hφ
  obtain ⟨f, rfl⟩ := hφ
  change ¬ T ^ N ∣ Polynomial.aeval T f at h
  show Polynomial.aeval T f ∣ T ^ N
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h (by simp)
  obtain ⟨q, hq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  simp only [map_zero, sub_zero] at hq hnd
  rw [Polynomial.X_dvd_iff] at hnd
  have hu : IsUnit (Polynomial.aeval T q) := by
    obtain ⟨r, hr⟩ : Polynomial.X ∣ q - Polynomial.C (q.coeff 0) :=
      Polynomial.X_dvd_iff.2 (by simp)
    have hq' : q = Polynomial.C (q.coeff 0) + Polynomial.X * r := sub_eq_iff_eq_add'.mp hr
    have hev : Polynomial.aeval T q = algebraMap k A (q.coeff 0) + T * Polynomial.aeval T r := by
      conv_lhs => rw [hq']
      simp
    have hnil : IsNilpotent (T * Polynomial.aeval T r) := by
      obtain ⟨M, hM⟩ := hT
      exact ⟨M, by rw [mul_pow, hM, zero_mul]⟩
    have hc : IsUnit (algebraMap k A (q.coeff 0)) := (Ne.isUnit hnd).map _
    rw [hev]
    first
      | exact hnil.isUnit_add_right_of_commute hc (Commute.all _ _)
      | (rw [add_comm]; exact hnil.isUnit_add_right_of_commute hc (Commute.all _ _))
  have hφ : Polynomial.aeval T f = T ^ Polynomial.rootMultiplicity 0 f * Polynomial.aeval T q := by
    conv_lhs => rw [hq]
    simp
  by_cases hv : N ≤ Polynomial.rootMultiplicity 0 f
  · exfalso
    exact h (hφ ▸ dvd_mul_of_dvd_left (pow_dvd_pow T hv) _)
  · push_neg at hv
    rw [hφ]
    refine ⟨↑hu.unit⁻¹ * T ^ (N - Polynomial.rootMultiplicity 0 f), ?_⟩
    calc T ^ N = T ^ Polynomial.rootMultiplicity 0 f * T ^ (N - Polynomial.rootMultiplicity 0 f) := by
          rw [← pow_add, Nat.add_sub_cancel' hv.le]
      _ = T ^ Polynomial.rootMultiplicity 0 f * Polynomial.aeval T q *
          (↑hu.unit⁻¹ * T ^ (N - Polynomial.rootMultiplicity 0 f)) := by
          rw [mul_assoc, ← mul_assoc (Polynomial.aeval T q), hu.mul_val_inv, one_mul]

theorem UpperTheory.V.FW.phiDvd :
    ∀ (l : ℕ) [Fact l.Prime] (b K : ℕ) (k G Q : Type) [Field k] [CharP k l] [CommGroup G] [CommGroup Q] (p : G →* G) (π : G →* Q) (γ : G) (χ : G →* kˣ) (θ : MonoidAlgebra k G), γ ^ l ^ b = 1 → (∀ g, p g ∈ Subgroup.zpowers γ) → (∀ g, π (p g) = π g) → π γ ^ l ^ K = 1 → tw χ π θ ≠ 0 → tw χ p θ ∣ (MonoidAlgebra.of k G γ - 1) ^ l ^ K := by
  intro l _ b K k G Q _ _ _ _ p π γ χ θ hγ hp hπ hπγ hne
  set T : MonoidAlgebra k G := MonoidAlgebra.of k G γ - 1 with hT
  have hof : ∀ m : ℕ, MonoidAlgebra.of k G (γ ^ m) ∈ Algebra.adjoin k {T} := by
    intro m
    have e : MonoidAlgebra.of k G (γ ^ m) = (T + 1) ^ m := by rw [hT, sub_add_cancel, map_pow]
    rw [e]
    exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (Algebra.self_mem_adjoin_singleton k T) (Subalgebra.one_mem _)) _
  have hfin : IsOfFinOrder γ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ b, pow_pos (Fact.out : l.Prime).pos _, hγ⟩
  have hmem : tw χ p θ ∈ Algebra.adjoin k {T} := by
    rw [← MonoidAlgebra.sum_coeff_single θ, map_finsuppSum, Finsupp.sum]
    refine Subalgebra.sum_mem _ fun g _ => ?_
    rw [tw_single]
    obtain ⟨m, hm⟩ := (hfin.mem_powers_iff_mem_zpowers).2 (hp g)
    have e : MonoidAlgebra.single (p g) (θ.coeff g * ↑(χ g)) =
        (θ.coeff g * ↑(χ g)) • MonoidAlgebra.of k G (γ ^ m) := by
      rw [← (show γ ^ m = p g from hm), MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    rw [e]
    exact Subalgebra.smul_mem _ (hof m) _
  have hTnil : IsNilpotent T :=
    ⟨l ^ b, by rw [hT, phiDvd_pow l b k, ← map_pow, hγ, map_one, sub_self]⟩
  refine phiDvd_nil k _ T _ hTnil hmem _ ?_
  intro hdvd
  apply hne
  set ψ := MonoidAlgebra.mapDomainAlgHom k k π with hψ
  have hcomp : ψ.comp (tw χ p) = tw χ π := by
    refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
    simp [hψ, tw_single, hπ]
  have hψT : ψ T ^ l ^ K = 0 := by
    rw [← map_pow, hT, phiDvd_pow l K k, map_sub, map_pow, map_one]
    simp [hψ, MonoidAlgebra.of_apply, MonoidAlgebra.single_pow, ← map_pow, hπγ, MonoidAlgebra.one_def]
  obtain ⟨c, hc⟩ := hdvd
  have h1 : tw χ π θ = ψ (tw χ p θ) := by rw [← hcomp]; rfl
  rw [h1, hc, map_mul, map_pow, hψT, zero_mul]
end

section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinFin :
    ∀ (k ι : Type) [CommRing k] [Fintype ι] [DecidableEq ι] (m : ℕ) [NeZero m] (η : ι → (ZMod m)ˣ) (N : ℕ) (P : ℕ → k) (α : ZMod m → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod m) = y then P s else 0) → (∀ y, ∑ i, α (((η i)⁻¹ : (ZMod m)ˣ) * y) = 0) → sinE (fun i => (η i : ZMod m)) N P = 0 := by
  intro k ι _ _ _ m _ η N P α hα hsum
  have hsingSum : ∀ (z : ZMod m) (t : Finset ℕ) (g : ℕ → k),
      AddMonoidAlgebra.single z (∑ s ∈ t, g s) = ∑ s ∈ t, AddMonoidAlgebra.single z (g s) :=
    fun z t g => map_sum (AddMonoidAlgebra.singleAddHom z) g t
  have hsingSumι : ∀ (z : ZMod m) (g : ι → k),
      AddMonoidAlgebra.single z (∑ i, g i) = ∑ i, AddMonoidAlgebra.single z (g i) :=
    fun z g => map_sum (AddMonoidAlgebra.singleAddHom z) g Finset.univ
  have hsingSub : ∀ (z : ZMod m) (a b : k),
      AddMonoidAlgebra.single z (a - b) = AddMonoidAlgebra.single z a - AddMonoidAlgebra.single z b :=
    fun z a b => map_sub (AddMonoidAlgebra.singleAddHom z) a b
  set A : ι → AddMonoidAlgebra k (ZMod m) :=
    fun i => ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y) with hA
  have hS : ∀ i, (∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s)) =
      (1 - AddMonoidAlgebra.single (N • (η i : ZMod m)) 1) * A i := by
    intro i
    have hone : ∀ s : ℕ, ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y)
        (if (s : ZMod m) = y then P s else 0) = AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) := by
      intro s
      rw [Finset.sum_eq_single (s : ZMod m)]
      · simp [nsmul_eq_mul, mul_comm]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    have e1 : ∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y - α (y - N)) := by
      simp_rw [hα, hsingSum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => (hone s).symm
    have e2 : ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α (y - N)) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [← Equiv.sum_comp (Equiv.addRight (N : ZMod m))]
      simp
    have e3 : AddMonoidAlgebra.single (N • (η i : ZMod m)) (1 : k) * A i =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [AddMonoidAlgebra.single_mul_single, one_mul, nsmul_eq_mul]
      congr 1
      ring
    rw [e1, sub_mul, one_mul, e3, ← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => hsingSub _ _ _
  have hA0 : ∑ i, A i = 0 := by
    have hre : ∀ i, A i = ∑ z : ZMod m,
        AddMonoidAlgebra.single z (α (((η i)⁻¹ : (ZMod m)ˣ) * z)) := by
      intro i
      rw [hA, ← Equiv.sum_comp (Units.mulLeft (η i))]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp
    simp_rw [hre]
    rw [Finset.sum_comm]
    simp_rw [← hsingSumι, hsum]
    simp
  unfold sinE
  dsimp only
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [hS i, mul_assoc, mul_left_comm, Finset.mul_prod_erase Finset.univ
      (fun j => 1 - AddMonoidAlgebra.single (N • (η j : ZMod m)) (1 : k)) (Finset.mem_univ i)])]
  rw [← Finset.sum_mul, hA0, zero_mul]
end

section

open UpperTheory.V.FW

private theorem prod_single_eq_single_sum {k A ι : Type} [CommRing k] [AddCommGroup A] [DecidableEq ι]
    (T : Finset ι) (f : ι → A) (c : k) :
    ∏ j ∈ T, (AddMonoidAlgebra.single (f j) c : AddMonoidAlgebra k A)
      = AddMonoidAlgebra.single (∑ j ∈ T, f j) (∏ _j ∈ T, c) := by
  induction T using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, ih, AddMonoidAlgebra.single_mul_single, Finset.sum_insert hi,
      Finset.prod_insert hi]

private theorem coeff_monic_poly_sum {k A ι : Type} [CommRing k] [AddCommGroup A]
    (T : Finset ι) (f : ι → AddMonoidAlgebra k A) (a : A) (h : (∑ j ∈ T, f j).coeff a ≠ 0) :
    ∃ j ∈ T, (f j).coeff a ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero hc

theorem UpperTheory.V.FW.sinSupp :
    ∀ (A ι : Type) [AddCommGroup A] [Fintype ι] [DecidableEq ι] (η : ι → A) (N : ℕ), ∃ S : Finset A, ∀ (k : Type) [CommRing k] (P : ℕ → k) (a : A), (sinE η N P).coeff a ≠ 0 → a ∈ S := by
  intro A ι _ _ _ η N
  classical
  refine ⟨(Finset.univ ×ˢ (Finset.range N ×ˢ (Finset.univ : Finset ι).powerset)).image
    (fun p : ι × ℕ × Finset ι => p.2.1 • η p.1 + ∑ j ∈ p.2.2, N • η j), ?_⟩
  intro k _ P a ha
  simp only [sinE] at ha
  obtain ⟨i, -, hi⟩ := coeff_monic_poly_sum _ _ a ha
  have hprod : ∏ j ∈ Finset.univ.erase i, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
      = ∑ t ∈ (Finset.univ.erase i).powerset,
          AddMonoidAlgebra.single (∑ j ∈ t, N • η j) (∏ _j ∈ t, (-1 : k)) := by
    have e : ∀ j, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
        = AddMonoidAlgebra.single (N • η j) (-1 : k) + 1 := by
      intro j
      rw [AddMonoidAlgebra.single_neg]
      abel
    simp_rw [e]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_const_one, mul_one, prod_single_eq_single_sum]
  rw [hprod, Finset.sum_mul] at hi
  obtain ⟨s, hs, hs2⟩ := coeff_monic_poly_sum _ _ a hi
  rw [Finset.mul_sum] at hs2
  obtain ⟨t, ht, ht2⟩ := coeff_monic_poly_sum _ _ a hs2
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single_apply] at ht2
  split_ifs at ht2 with hEq
  · rw [Finset.mem_image]
    refine ⟨(i, s, t), ?_, hEq⟩
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_powerset, true_and]
    exact ⟨hs, Finset.subset_univ _⟩
  · exact absurd rfl ht2
end

section

open UpperTheory.V.FW

private theorem pOdd_relIndex_le (l : ℕ) (C : Type) [CommGroup C] [Finite C] (B : Subgroup C) :
    (powR (C := C) l).relIndex B ≤ Nat.card (B ⊓ torK (C := C) l : Subgroup C) := by
  have h1 : powR (C := B) l ≤ (powR (C := C) l).subgroupOf B := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(y : C), by simp⟩
  have h2 : ((powR (C := C) l).subgroupOf B).index ≤ (powR (C := B) l).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le h1)
  have h3 : (powR (C := B) l).index = Nat.card (torK (C := B) l) := by
    have a := Subgroup.index_mul_card (powR (C := B) l)
    have b := Subgroup.index_mul_card (torK (C := B) l)
    have c : (torK (C := B) l).index = Nat.card (powR (C := B) l) := Subgroup.index_ker _
    have d : 0 < Nat.card (powR (C := B) l) := Nat.card_pos
    rw [c, ← a, mul_comm] at b
    exact (Nat.eq_of_mul_eq_mul_right d b).symm
  have h4 : Nat.card (torK (C := B) l) ≤ Nat.card (B ⊓ torK (C := C) l : Subgroup C) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : C), x.1.2, ?_⟩ : (B ⊓ torK (C := C) l : Subgroup C))) ?_
    · have hx : x.1 ^ l = 1 := x.2
      show (x.1 : C) ^ l = 1
      rw [← Subgroup.coe_pow, hx]; rfl
    · intro x y hxy
      have e := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext e)
  exact h2.trans (h3.le.trans h4)

theorem UpperTheory.V.FW.pOdd :
    ∀ (l : ℕ) (C : Type) [CommGroup C] [Finite C] (J : C →* C), Odd l → (powR (C := C) l ⊔ difR J).index ≤ l * Nat.card (minK J ⊓ torK (C := C) l : Subgroup C) → (powR (C := C) l).index ≤ l * Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) ^ 2 := by
  intro l C _ _ J hl h
  obtain ⟨k, hk⟩ := hl
  have h1 : minK J ⊓ torK (C := C) l ≤ difR J ⊓ torK (C := C) l := by
    rintro x ⟨hx, hx'⟩
    refine ⟨⟨x ^ (k + 1), ?_⟩, hx'⟩
    have a : J x * x = 1 := hx
    have b : x ^ l = 1 := hx'
    have c : J x = x⁻¹ := eq_inv_of_mul_eq_one_left a
    show x ^ (k + 1) / J (x ^ (k + 1)) = x
    rw [map_pow, c, inv_pow, div_inv_eq_mul, ← pow_add,
      show k + 1 + (k + 1) = l + 1 by omega, pow_succ, b, one_mul]
  have h2 : Nat.card (minK J ⊓ torK (C := C) l : Subgroup C) ≤ Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) :=
    Subgroup.card_le_of_le h1
  have h3 := Subgroup.relIndex_mul_index (le_sup_left : powR (C := C) l ≤ powR (C := C) l ⊔ difR J)
  rw [Subgroup.relIndex_sup_left] at h3
  have h4 := pOdd_relIndex_le l C (difR J)
  calc (powR (C := C) l).index = (powR (C := C) l).relIndex (difR J) * (powR (C := C) l ⊔ difR J).index := h3.symm
    _ ≤ Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) * (l * Nat.card (difR J ⊓ torK (C := C) l : Subgroup C)) :=
      Nat.mul_le_mul h4 (h.trans (Nat.mul_le_mul_left _ h2))
    _ = _ := by ring
end

section

open UpperTheory.V.FW

private theorem padic_val_one_add_mul_pow_pow_sub_one (l : ℕ) (hl : l.Prime) (f : ℕ) (hf : f.Coprime l) (j : ℕ) :
    (l : ℤ) ^ (ee l + j) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 ∧
      ¬ (l : ℤ) ^ (ee l + j + 1) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hfl : ¬ (l : ℤ) ∣ (f : ℤ) := by
    intro hd
    have hd' : l ∣ f := Int.natCast_dvd_natCast.mp hd
    exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hf.symm hd')
  have hq : emultiplicity (l : ℤ) ((f : ℤ) * (l : ℤ) ^ ee l) = (ee l : ℕ∞) := by
    rw [emultiplicity_mul hp, emultiplicity_pow_self_of_prime hp, emultiplicity_eq_zero.mpr hfl,
      zero_add]
  have hx : ¬ (l : ℤ) ∣ 1 + (f : ℤ) * (l : ℤ) ^ ee l := by
    intro hd
    have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
    have h2 : (l : ℤ) ∣ (f : ℤ) * (l : ℤ) ^ ee l :=
      Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    have h3 : (l : ℤ) ∣ 1 := by
      have := dvd_sub hd h2
      simpa using this
    have h4 : l ∣ 1 := by exact_mod_cast h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h4)
  have key : emultiplicity (l : ℤ) ((1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1)
      = ((ee l + j : ℕ) : ℕ∞) := by
    by_cases h2 : l = 2
    · subst h2
      have e2 : ee 2 = 2 := by simp [ee]
      have h4 : (4 : ℤ) ∣ (1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) - 1 := by
        rw [e2]
        exact ⟨f, by push_cast; ring⟩
      have hx2 : ¬ (2 : ℤ) ∣ 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2 := by
        simpa using hx
      have := Int.two_pow_two_pow_sub_pow_two_pow (x := 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2)
        (y := 1) j h4 hx2
      rw [one_pow, add_sub_cancel_left] at this
      have hq2 : emultiplicity (2 : ℤ) ((f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) = (ee 2 : ℕ∞) := by
        simpa using hq
      rw [hq2] at this
      have : emultiplicity ((2 : ℕ) : ℤ) ((1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) ^ 2 ^ j - 1)
          = (ee 2 : ℕ∞) + j := by simpa using this
      rw [this]
      push_cast
      rfl
    · have hodd : Odd l := hl.odd_of_ne_two h2
      have e1 : ee l = 1 := by simp [ee, h2]
      have hxy : (l : ℤ) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) - 1 := by
        rw [add_sub_cancel_left]
        exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
      have := Int.emultiplicity_pow_sub_pow hl hodd hxy hx (l ^ j)
      rw [one_pow, add_sub_cancel_left, hq,
        emultiplicity_pow_self_of_prime (Nat.prime_iff.mp hl) j] at this
      rw [this]
      push_cast
      rfl
  constructor
  · rw [pow_dvd_iff_le_emultiplicity, key]
  · rw [pow_dvd_iff_le_emultiplicity, key]
    norm_cast
    omega


theorem UpperTheory.V.FW.gamGen :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (γ : (ZMod (f * l ^ n))ˣ), f.Coprime l → ee l ≤ n → (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l → (ZMod.unitsMap h).ker = Subgroup.zpowers γ ∧ γ ^ l ^ n = 1 := by
  intro l _ f n h γ hf hen hγ
  have hl : l.Prime := Fact.out
  obtain ⟨d, rfl⟩ : ∃ d, n = ee l + d := ⟨n - ee l, by omega⟩
  have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : l = 1 := by simpa [Nat.Coprime] using hf
    exact hl.one_lt.ne' this
  haveI : NeZero (f * l ^ (ee l + d)) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (f * l ^ ee l) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  set x : ℤ := 1 + (f : ℤ) * (l : ℤ) ^ ee l with hxdef
  have hγx : (γ : ZMod (f * l ^ (ee l + d))) = ((x : ℤ) : ZMod (f * l ^ (ee l + d))) := by
    rw [hγ, hxdef]
    push_cast
    ring
  have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ (ee l + d)) := by
    rw [← Int.natCast_pow, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ hf
  have hpow : ∀ m : ℕ, γ ^ m = 1 ↔ (l : ℤ) ^ (ee l + d) ∣ x ^ m - 1 := by
    intro m
    have hfdvd : (f : ℤ) ∣ x ^ m - 1 := by
      have h1 : x - 1 ∣ x ^ m - 1 ^ m := sub_dvd_pow_sub_pow x 1 m
      rw [one_pow] at h1
      refine dvd_trans ?_ h1
      rw [hxdef, add_sub_cancel_left]
      exact dvd_mul_right _ _
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, hγx, ← Int.cast_pow,
      ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    constructor
    · intro hd
      exact dvd_trans (dvd_mul_left _ _) hd
    · intro hd
      exact hcop.mul_dvd hfdvd hd
  have hord : orderOf γ = l ^ d := by
    rcases d with _ | d
    · rw [pow_zero, orderOf_eq_one_iff]
      have h1 : γ ^ (l ^ 0) = 1 := by
        rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf 0).1
      simpa using h1
    · apply orderOf_eq_prime_pow
      · rw [hpow, hxdef, ← Nat.add_assoc]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf d).2
      · rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf (d + 1)).1
  set K := (ZMod.unitsMap h).ker with hK
  have c1 : Nat.card (ZMod (f * l ^ (ee l + d)))ˣ = (f * l ^ (ee l + d)).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have c2 : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcardK : Nat.card K = l ^ d := by
    have a := Subgroup.card_mul_index K
    rw [hK, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective h),
      Subgroup.card_top, c1, c2,
      Nat.totient_mul (Nat.Coprime.pow_right _ hf), Nat.totient_mul (Nat.Coprime.pow_right _ hf),
      Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)] at a
    have hpos : 0 < f.totient * (l ^ (ee l - 1) * (l - 1)) := by
      have h1 := hl.one_lt
      have h2 := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hf0)
      exact Nat.mul_pos h2 (Nat.mul_pos (pow_pos hl.pos _) (by omega))
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hK, a]
    have : ee l + d - 1 = (ee l - 1) + d := by omega
    rw [this, pow_add]
    ring
  have hmem : γ ∈ K := by
    rw [hK, MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, Units.val_one,
      MonoidHom.coe_coe, hγ, map_add, map_one, map_mul, map_pow, map_natCast, map_natCast]
    have h0 : ((f * l ^ ee l : ℕ) : ZMod (f * l ^ ee l)) = 0 := ZMod.natCast_self _
    push_cast at h0
    rw [h0, add_zero]
  have hle : Subgroup.zpowers γ ≤ K := (Subgroup.zpowers_le).mpr hmem
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle ?_).symm, ?_⟩
  · rw [Nat.card_zpowers, hord, hcardK]
  · rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact pow_dvd_pow l (by omega)
end
