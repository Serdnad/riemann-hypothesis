module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

@[expose] public section

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem card_tors (W : Type) [AddCommGroup W] [Finite W] (l : ℤ) (s : ℕ) :
    Nat.card (Submodule.torsionBy ℤ W (l ^ s)) ≤ Nat.card {w : W // l • w = 0} ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    let T := Submodule.torsionBy ℤ W (l ^ (s + 1))
    let m : T →ₗ[ℤ] W := l • T.subtype
    have hr : LinearMap.range m ≤ Submodule.torsionBy ℤ W (l ^ s) := by
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_torsionBy_iff]
      have hw := (Submodule.mem_torsionBy_iff _ _).1 w.2
      change l ^ s • (l • (w : W)) = 0
      rw [smul_smul, ← pow_succ]
      exact hw
    have h1 : Nat.card T = Nat.card (T ⧸ LinearMap.ker m) * Nat.card (LinearMap.ker m) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker m).toAddSubgroup
    rw [Nat.card_congr m.quotKerEquivRange.toEquiv] at h1
    have h2 : Nat.card (LinearMap.range m) ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) :=
      Nat.card_le_card_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
    have h3 : Nat.card (LinearMap.ker m) ≤ Nat.card {w : W // l • w = 0} :=
      Nat.card_le_card_of_injective (fun k => ⟨((k : T) : W), k.2⟩)
        (fun a b hab => by
          have h := congrArg Subtype.val hab
          apply Subtype.ext
          apply Subtype.ext
          exact h)
    calc Nat.card T = Nat.card (LinearMap.range m) * Nat.card (LinearMap.ker m) := h1
      _ ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul h2 h3
      _ ≤ Nat.card {w : W // l • w = 0} ^ s * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul_right _ ih
      _ = Nat.card {w : W // l • w = 0} ^ (s + 1) := (pow_succ _ _).symm

theorem UpperTheory.V.ZK.Ct.pCount :
    ∀ (W Z : Type) [AddCommGroup W] [AddCommGroup Z] [Finite W] (f : W →ₗ[ℤ] Z) (l s g : ℕ) (u : ℤ), l.Prime → ¬(l : ℤ) ∣ u → (∀ w, f w = 0 → (u * (l : ℤ) ^ s) • w = 0) → Nat.card {w : W // (l : ℤ) • w = 0} ≤ l ^ g → l ^ (Nat.card W).factorization l ≤ Nat.card (LinearMap.range f) * l ^ (s * g) := by
  intro W Z _ _ _ f l s g u hl hlu hker hW
  haveI := Fact.mk hl
  let K := LinearMap.ker f
  let gm : K →ₗ[ℤ] K := ((l : ℤ) ^ s) • LinearMap.id
  haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict
  have hWc : Nat.card W = Nat.card (LinearMap.range f) * Nat.card K := by
    have h : Nat.card W = Nat.card (W ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
    rwa [Nat.card_congr f.quotKerEquivRange.toEquiv] at h
  have hKc : Nat.card K = Nat.card (LinearMap.range gm) * Nat.card (LinearMap.ker gm) := by
    have h : Nat.card K = Nat.card (K ⧸ LinearMap.ker gm) * Nat.card (LinearMap.ker gm) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker gm).toAddSubgroup
    rwa [Nat.card_congr gm.quotKerEquivRange.toEquiv] at h
  have hR0 : Nat.card (LinearMap.range f) ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hRg0 : Nat.card (LinearMap.range gm) ≠ 0 := Nat.card_pos.ne'
  have hKg0 : Nat.card (LinearMap.ker gm) ≠ 0 := Nat.card_pos.ne'
  have hcop : ¬ l ∣ Nat.card (LinearMap.range gm) := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hd
    have hux : u • x = 0 := by
      rcases x with ⟨y, k, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      change u • ((l : ℤ) ^ s • ((k : K) : W)) = 0
      rw [smul_smul]
      exact hker _ k.2
    have hdv := addOrderOf_dvd_iff_zsmul_eq_zero.2 hux
    rw [hx] at hdv
    exact hlu hdv
  have hvK : (Nat.card K).factorization l = (Nat.card (LinearMap.ker gm)).factorization l := by
    rw [hKc, Nat.factorization_mul hRg0 hKg0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hcop, zero_add]
  have hA : Nat.card (LinearMap.ker gm) ≤ l ^ (s * g) := by
    calc Nat.card (LinearMap.ker gm) ≤ Nat.card (Submodule.torsionBy ℤ W ((l : ℤ) ^ s)) :=
          Nat.card_le_card_of_injective
            (fun a => ⟨((a : K) : W), by
              rw [Submodule.mem_torsionBy_iff]
              exact congrArg Subtype.val (LinearMap.mem_ker.1 a.2)⟩)
            (fun a b hab => by
              have h := congrArg Subtype.val hab
              apply Subtype.ext
              apply Subtype.ext
              exact h)
      _ ≤ Nat.card {w : W // (l : ℤ) • w = 0} ^ s := card_tors W l s
      _ ≤ (l ^ g) ^ s := Nat.pow_le_pow_left hW s
      _ = l ^ (s * g) := by rw [← pow_mul, mul_comm]
  have hR : l ^ (Nat.card (LinearMap.range f)).factorization l ≤ Nat.card (LinearMap.range f) :=
    Nat.ordProj_le l hR0
  have hKl : l ^ (Nat.card (LinearMap.ker gm)).factorization l ≤ Nat.card (LinearMap.ker gm) :=
    Nat.ordProj_le l hKg0
  rw [hWc, Nat.factorization_mul hR0 hK0, Finsupp.add_apply, pow_add, hvK]
  exact Nat.mul_le_mul hR (hKl.trans hA)
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem permDet_weight {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (ζ : ℂ) (hζ : ζ ^ n = 1) (hζ0 : ζ ≠ 0) :
    ∃ c : X → ℂ, (∀ x, c x ≠ 0) ∧ ∀ x, c (π x) = ζ * c x := by
  classical
  let S := Equiv.Perm.SameCycle.setoid π
  have hk : ∀ x : X, ∃ k : ℕ, (π ^ k) (Quotient.out (Quotient.mk S x)) = x := fun x => by
    have hr : π.SameCycle (Quotient.out (Quotient.mk S x)) x := Quotient.mk_out (s := S) x
    obtain ⟨i, _, hi⟩ := hr.exists_pow_eq'
    exact ⟨i, hi⟩
  choose k hk using hk
  have hsame : ∀ y : X, ∀ p q : ℕ, (π ^ p) y = (π ^ q) y → ζ ^ p = ζ ^ q := by
    intro y p q hpq
    wlog hle : p ≤ q generalizing p q
    · exact (this q p hpq.symm (by omega)).symm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hfix : (π ^ d) ((π ^ p) y) = (π ^ p) y := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
      exact hpq.symm
    obtain ⟨m, rfl⟩ := (h d _).1 hfix
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  refine ⟨fun x => ζ ^ k x, fun x => pow_ne_zero _ hζ0, fun x => ?_⟩
  have hq : Quotient.mk S (π x) = Quotient.mk S x :=
    Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl π x))
  have e1 := hk (π x)
  rw [hq] at e1
  have e2 : (π ^ (k x + 1)) (Quotient.out (Quotient.mk S x)) = π x := by
    rw [pow_succ', Equiv.Perm.mul_apply, hk x]
  show ζ ^ k (π x) = ζ * ζ ^ k x
  rw [← pow_succ']
  exact hsame _ _ _ (e1.trans e2.symm)

private theorem permDet_twist {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X)
    (ζ a : ℂ) (c : X → ℂ) (hc0 : ∀ x, c x ≠ 0) (hc : ∀ x, c (π x) = ζ * c x) :
    (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ).det = (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
  have key : Matrix.diagonal c * (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ) * Matrix.diagonal c := by
    ext i j
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Matrix.one_apply]
    by_cases h2 : π i = j
    · subst h2
      rw [hc]
      by_cases h1 : i = π i
      · have e := hc i
        rw [← h1] at e
        have hz : ζ = 1 := mul_right_cancel₀ (hc0 i) (e.symm.trans (one_mul _).symm)
        rw [if_pos h1, if_pos rfl, if_pos rfl, hz]
        ring
      · rw [if_neg h1, if_pos rfl, if_pos rfl]
        ring
    · rw [if_neg h2, if_neg h2]
      split_ifs with h1
      · subst h1
        ring
      · ring
  have hd : (Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hc0 x
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm ((a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det)] at this
  exact mul_left_cancel₀ hd this

private theorem permDet_pow {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (hn : 0 < n) (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (a : ℂ) :
    (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det ^ n = (a ^ n - 1) ^ Fintype.card X := by
  classical
  have hpow : ∀ k : ℕ, (π.permMatrix ℂ) ^ k = (π ^ k).permMatrix ℂ := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.permMatrix_one]
    | succ k ih => rw [pow_succ', pow_succ, Matrix.permMatrix_mul, ih]
  have hπn : π ^ n = 1 := Equiv.ext fun x => (h n x).2 dvd_rfl
  have hPn : (π.permMatrix ℂ) ^ n = 1 := by rw [hpow, hπn, Matrix.permMatrix_one]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨S, hS⟩ : ∃ S, S = Polynomial.nthRootsFinset n (1 : ℂ) := ⟨_, rfl⟩
  have hcard : S.card = n := by rw [hS]; exact hprim.card_nthRootsFinset
  have hmem : ∀ ζ ∈ S, ζ ^ n = 1 := fun ζ hζ => by
    rw [hS] at hζ
    exact (Polynomial.mem_nthRootsFinset hn 1).1 hζ
  have hpt : ∀ t : ℂ, ∏ ζ ∈ S, (a - ζ * t) = a ^ n - t ^ n := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [Finset.prod_const, hcard, hn.ne']
    · have e := congrArg (Polynomial.eval (a / t)) (Polynomial.X_pow_sub_one_eq_prod hn hprim)
      rw [← hS] at e
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_prod, Polynomial.eval_C] at e
      have e2 : ∏ ζ ∈ S, (a - ζ * t) = ∏ ζ ∈ S, (t * (a / t - ζ)) :=
        Finset.prod_congr rfl fun ζ _ => by field_simp
      rw [e2, Finset.prod_mul_distrib, Finset.prod_const, hcard, ← e, div_pow]
      field_simp
  have hpoly : ∏ ζ ∈ S, (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      Polynomial.C (a ^ n) - Polynomial.X ^ n := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    exact hpt t
  let f : Polynomial ℂ →* ℂ :=
    Matrix.detMonoidHom.comp (Polynomial.aeval (π.permMatrix ℂ)).toRingHom.toMonoidHom
  have hf : ∀ q, f q = (Polynomial.aeval (π.permMatrix ℂ) q).det := fun q => rfl
  have hdet := congrArg f hpoly
  rw [map_prod, hf] at hdet
  have hfac : ∀ ζ ∈ S, f (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    intro ζ hζ
    have hz0 : ζ ≠ 0 := by
      rintro rfl
      have := hmem 0 hζ
      rw [zero_pow hn.ne'] at this
      exact zero_ne_one this
    obtain ⟨c, hc0, hc⟩ := permDet_weight π n h ζ (hmem ζ hζ) hz0
    rw [hf, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact permDet_twist π ζ a c hc0 hc
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, hcard] at hdet
  rw [hdet, map_sub, Polynomial.aeval_C, Polynomial.aeval_X_pow, hPn, Algebra.algebraMap_eq_smul_one]
  have e3 : (a ^ n • (1 : Matrix X X ℂ) - 1) = (a ^ n - 1) • (1 : Matrix X X ℂ) := by
    rw [sub_smul, one_smul]
  rw [e3, Matrix.det_smul, Matrix.det_one, mul_one]

theorem UpperTheory.V.ZK.Ct.permDet :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n r : ℕ) (a : ℝ), 0 < n → 1 ≤ a → Fintype.card X = n * r → (∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) → |LinearMap.det (LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)))| = (a ^ n - 1) ^ r := by
  intro X _ _ π n r a hn ha hcard h
  classical
  have hlin : LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)) =
      Matrix.toLin' (π.permMatrix ℝ - a • (1 : Matrix X X ℝ)) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.permMatrix_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rfl
  rw [hlin, LinearMap.det_toLin']
  have hneg : π.permMatrix ℝ - a • (1 : Matrix X X ℝ) = -(a • (1 : Matrix X X ℝ) - π.permMatrix ℝ) := by
    rw [neg_sub]
  rw [hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hC := permDet_pow π n hn h (a : ℂ)
  have hmap : ((a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det : ℂ) =
      ((a : ℂ) • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    have e := RingHom.map_det Complex.ofRealHom (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ)
    rw [Complex.ofRealHom_eq_coe] at e
    rw [e]
    congr 1
    ext i j
    simp [Matrix.one_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  have hR : (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det ^ n = ((a ^ n - 1) ^ r) ^ n := by
    apply Complex.ofReal_injective
    push_cast
    rw [hmap, hC, hcard, pow_mul']
  have hnn : 0 ≤ a ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ ha)
  rw [← pow_left_inj₀ (abs_nonneg _) (pow_nonneg hnn r) hn.ne', ← abs_pow, hR,
    abs_of_nonneg (pow_nonneg (pow_nonneg hnn r) n)]
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem padic_val_one_add_pow_sub_one (l c m : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (h2 : l = 2 → 2 ≤ c)
    (hm : m ≠ 0) : padicValNat l ((1 + l ^ c) ^ m - 1) = c + padicValNat l m := by
  simp only [Nat.padicValNat_def]
  haveI := Fact.mk hl
  have hpow1 : 1 ≤ l ^ c := Nat.one_le_pow c l hl.pos
  have hx1 : 1 < 1 + l ^ c := by omega
  have hdvd : l ∣ (1 + l ^ c) - 1 := by
    rw [Nat.add_sub_cancel_left]
    exact dvd_pow_self l (by omega)
  have hnd : ¬ l ∣ 1 + l ^ c := by
    intro h
    rw [add_comm] at h
    have := (Nat.dvd_add_right (dvd_pow_self l (by omega : c ≠ 0))).1 h
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by have := h2 rfl; omega⟩
    have h4 : 2 ^ (d + 2) = 4 * 2 ^ d := by ring
    have h := padicValNat.pow_two_sub_pow (x := 1 + 2 ^ (d + 2)) (y := 1) hx1 hdvd hnd
      (n := 2 * m) (by omega) (even_two_mul m)
    rw [one_pow] at h
    have hA : multiplicity 2 (1 + 2 ^ (d + 2) + 1) = 1 := by
      have e : 1 + 2 ^ (d + 2) + 1 = 2 * (1 + 2 * 2 ^ d) := by rw [h4]; ring
      rw [e, Nat.multiplicity_mul (by norm_num) (by omega), Nat.multiplicity_self (by norm_num),
        (Nat.multiplicity_eq_zero_iff.mpr (Or.inr (Or.inr (by omega))))]
    have hB : multiplicity 2 (1 + 2 ^ (d + 2) - 1) = d + 2 := by
      rw [Nat.add_sub_cancel_left, Nat.multiplicity_prime_pow]
    have hC : multiplicity 2 (2 * m) = 1 + multiplicity 2 m := by
      rw [Nat.multiplicity_mul (by norm_num) hm, Nat.multiplicity_self (by norm_num)]
    have hxm : 1 < (1 + 2 ^ (d + 2)) ^ m := Nat.one_lt_pow hm hx1
    obtain ⟨b, hb⟩ : ∃ b, (1 + 2 ^ (d + 2)) ^ m = b + 1 := ⟨_ - 1, (Nat.sub_add_cancel hxm.le).symm⟩
    have hmod : (1 + 2 ^ (d + 2)) ^ m % 4 = 1 := by
      rw [Nat.pow_mod, h4]
      have : (1 + 4 * 2 ^ d) % 4 = 1 := by omega
      rw [this, one_pow]
      rfl
    have hD : multiplicity 2 ((1 + 2 ^ (d + 2)) ^ m + 1) = 1 := by
      obtain ⟨q, hq⟩ : ∃ q, (1 + 2 ^ (d + 2)) ^ m + 1 = 2 * (2 * q + 1) :=
        ⟨((1 + 2 ^ (d + 2)) ^ m + 1) / 4, by omega⟩
      rw [hq, Nat.multiplicity_mul (by norm_num) (by omega), Nat.multiplicity_self (by norm_num),
        (Nat.multiplicity_eq_zero_iff.mpr (Or.inr (Or.inr (by omega))))]
    have hfac : (1 + 2 ^ (d + 2)) ^ (2 * m) - 1 =
        ((1 + 2 ^ (d + 2)) ^ m - 1) * ((1 + 2 ^ (d + 2)) ^ m + 1) := by
      rw [pow_mul', hb, Nat.add_sub_cancel]
      have : (b + 1) ^ 2 = b * (b + 1 + 1) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
    rw [hfac, Nat.multiplicity_mul (by omega) (by omega), hD, hA, hB, hC] at h
    omega
  · have := padicValNat.pow_sub_pow hodd hx1 hdvd hnd hm
    rwa [one_pow, Nat.add_sub_cancel_left, Nat.multiplicity_prime_pow] at this

theorem UpperTheory.V.ZK.Ct.lte :
    ∀ l c ν E : ℕ, l.Prime → 1 ≤ c → (l = 2 → 2 ≤ c) → c ≤ ν → 1 ≤ E → 2 ≤ (1 + l ^ c) ^ E ∧ ((1 + l ^ c) ^ E - 1).factorization l = c + E.factorization l ∧ (((1 + l ^ c) ^ E) ^ l ^ (ν - c) - 1).factorization l = ν + E.factorization l := by
  intro l c ν E hl hc h2 hcν hE
  haveI := Fact.mk hl
  have hE0 : E ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have : 2 ≤ 1 + l ^ c := by have := Nat.one_le_pow c l hl.pos; omega
    exact this.trans (Nat.le_self_pow hE0 _)
  · rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl]
    simpa only [← Nat.padicValNat_def] using padic_val_one_add_pow_sub_one l c E hl hc h2 hE0
  · have hval := padic_val_one_add_pow_sub_one l c (E * l ^ (ν - c)) hl hc h2
      (mul_ne_zero hE0 (pow_ne_zero _ hl.ne_zero))
    simp only [Nat.padicValNat_def] at hval
    rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl, ← pow_mul, hval,
      Nat.multiplicity_mul hE0 (pow_ne_zero _ hl.ne_zero), Nat.multiplicity_prime_pow]
    omega
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.places :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F), IsTotallyComplex L → IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → IsTotallyComplex F ∧ Fintype.card (InfinitePlace F) = orderOf γ * InfinitePlace.nrComplexPlaces L ∧ ∀ (k : ℕ) (w : InfinitePlace F), γ ^ k • w = w ↔ orderOf γ ∣ k := by
  intro L F _ _ _ _ _ γ hL hG hγ
  haveI := hL
  haveI : IsTotallyComplex F := isTotallyComplex_of_algebra L F
  haveI : IsUnramifiedAtInfinitePlaces L F :=
    ⟨fun w => InfinitePlace.isUnramified_iff.mpr (Or.inr (IsTotallyComplex.isComplex _))⟩
  have htop : Subgroup.zpowers γ = ⊤ := eq_top_iff.mpr fun σ _ => hγ σ
  have hcard : Module.finrank L F = orderOf γ := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_zpowers, htop, Subgroup.card_top]
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [IsUnramifiedAtInfinitePlaces.card_infinitePlace L F, hcard,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, mul_comm]
  · intro k w
    have hst := (InfinitePlace.isUnramified L w).stabilizer_eq_bot
    rw [orderOf_dvd_iff_pow_eq_one, ← MulAction.mem_stabilizer_iff, hst, Subgroup.mem_bot]
end
