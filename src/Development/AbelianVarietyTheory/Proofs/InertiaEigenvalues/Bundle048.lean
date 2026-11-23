module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Norm.Defs
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_dvd_X_pow_card_sub_one_exists_root :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]),
      f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 →
        ∃ y : S, f.eval y = 0 := by
  intro S _ _ _ f hmon hdeg hdvd
  classical
  letI : Fintype (ResidueField S) := Fintype.ofFinite _
  have hQ : Nat.card (ResidueField S) = Fintype.card (ResidueField S) := Nat.card_eq_fintype_card
  set Q := Fintype.card (ResidueField S) with hQdef
  set g : (ResidueField S)[X] := f.map (residue S) with hgdef
  have hgm : g.Monic := hmon.map _
  have hgdeg : g.natDegree ≠ 0 := by rw [hgdef, hmon.natDegree_map]; exact hdeg
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hdvd' : g ∣ X ^ Q - X := by
    have h1 : g ∣ X ^ (Q - 1) - 1 := by
      have := Polynomial.map_dvd (residue S) hdvd
      simpa [hQ, g] using this
    have : (X ^ Q - X : (ResidueField S)[X]) = X * (X ^ (Q - 1) - 1) := by
      conv_lhs => rw [show Q = (Q - 1) + 1 by omega]
      ring
    rw [this]; exact dvd_mul_of_dvd_right h1 _
  have hne : (X ^ Q - X : (ResidueField S)[X]) ≠ 0 :=
    Polynomial.X_pow_sub_X_ne_zero hQ1
  have hsplit : Splits (X ^ Q - X : (ResidueField S)[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      Polynomial.natDegree_X_pow_sub_X (R := (ResidueField S)) hQ1]
    simp [Q]
  have hgs : Splits g := hsplit.of_dvd hne hdvd'
  obtain ⟨abar, habar⟩ := hgs.exists_eval_eq_zero
    (by rw [degree_eq_natDegree hgm.ne_zero]; exact_mod_cast hgdeg)
  have hchar : ringChar (ResidueField S) ∣ Q := by
    apply (ringChar.spec (ResidueField S) Q).mp
    exact FiniteField.cast_card_eq_zero (ResidueField S)
  have hsep : (X ^ Q - X : (ResidueField S)[X]).Separable :=
    galois_poly_separable (ringChar (ResidueField S)) Q hchar
  have hgsep := hsep.of_dvd hdvd'
  have hder : eval abar (derivative g) ≠ 0 := by
    have := hgsep.aeval_derivative_ne_zero (S := ResidueField S) (x := abar)
      (by simpa [aeval_def] using habar)
    simpa [aeval_def] using this
  obtain ⟨a, rfl⟩ := residue_surjective abar
  have key : ∀ p : S[X], residue S (p.eval a) = (p.map (residue S)).eval (residue S a) := by
    intro p; rw [eval_map, eval₂_hom]
  obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian f hmon a
    (by rw [← residue_eq_zero_iff, key]; exact habar)
    (by
      rw [← residue_ne_zero_iff_isUnit, key, ← derivative_map]
      exact hder)
  exact ⟨y, hy⟩

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem isBaseChange_subtype_of_basis_after_extension : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  intro S A EE O W RW D Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a ι c jD hinj hunit hjD ha d r o ho
    ⟨b⟩ q x hq huniq N hN
  classical
  subst hq
  have hxN : ∀ i, x i ∈ N := by
    intro i
    refine (hN _).2 ⟨Pi.single i 1, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hjsum : ∀ e : Fin (d * r) → EE, ∀ v : Fin (d * r) → D,
      jD (∑ i, e i • v i) = ∑ i, ι (e i) • jD (v i) := by
    intro e v

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hjD _ _

  have hspan : ∀ y : D, y ∈ Submodule.span EE (Set.range x) := by
    choose e' he' hdec using ho
    choose w' hw' using he'
    let u : Fin (d * r) → D := fun l =>
      algebraMap O EE (o (finProdFinEquiv.symm l).1) • b (finProdFinEquiv.symm l).2
    let C' : Matrix (Fin (d * r)) (Fin (d * r)) EE := fun i l =>
      e' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    let C : Matrix (Fin (d * r)) (Fin (d * r)) W := fun i l =>
      w' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    have hCC : ∀ i l, c (C i l) = ι (C' i l) := fun i l => hw' _ _
    have hx : ∀ i, x i = ∑ l, C' i l • u l := by
      intro i
      rw [← finProdFinEquiv.sum_comp]
      simp only [C', u, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      conv_lhs => rw [← b.sum_repr (x i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hdec (b.repr (x i) k)]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, Algebra.smul_def, mul_comm]
    choose B hB using fun l => (huniq (jD (u l))).exists
    have hCB : C * Matrix.of B = 1 := by
      ext i m
      have h1 : jD (x i) = ∑ m, c ((C * Matrix.of B) i m) • jD (x m) := by
        conv_lhs => rw [hx i, hjsum]

        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.of_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hB l, Finset.smul_sum, ← hCC]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul]
      have h2 : jD (x i) = ∑ m, c ((1 : Matrix _ _ W) i m) • jD (x m) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      exact congrFun ((huniq _).unique h1 h2) m
    have hdetC : IsUnit C.det := Matrix.isUnit_det_of_right_inverse hCB
    have hdetC' : IsUnit C'.det := by
      apply hunit
      have h1 : ι C'.det = c C.det := by
        rw [RingHom.map_det, AlgHom.map_det]
        congr 1
        ext i l
        simp [hCC]
      rw [h1]
      exact hdetC.map c
    have hu : ∀ l, u l ∈ Submodule.span EE (Set.range x) := by
      intro l
      have h1 : u l = ∑ i, C'⁻¹ l i • x i := by
        have h2 : ∑ i, C'⁻¹ l i • x i = ∑ m, (C'⁻¹ * C') l m • u m := by
          simp only [Matrix.mul_apply, Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hx i, Finset.smul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [smul_smul]
        rw [h2, Matrix.nonsing_inv_mul _ hdetC', Finset.sum_eq_single l]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      rw [h1]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hb : ∀ k, b k ∈ Submodule.span EE (Set.range x) := by
      intro k
      have h1 : b k = ∑ j, e' 1 j • u (finProdFinEquiv (j, k)) := by
        conv_lhs => rw [← one_smul EE (b k), hdec 1, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [u, Equiv.symm_apply_apply]
        rw [smul_smul, Algebra.smul_def, mul_comm]
      rw [h1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu _)
    intro y
    rw [← b.sum_repr y]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hb k)

  have hnf : ∀ t : EE ⊗[A] N, ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
      t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N) := by
    let P : AddSubmonoid (EE ⊗[A] N) :=
      { carrier := {t | ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
          t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N)}
        zero_mem' := ⟨0, fun i => by simp, by simp⟩
        add_mem' := by
          rintro _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
          refine ⟨e₁ + e₂, fun i => ?_, ?_⟩
          · rw [Pi.add_apply, map_add (f := _)]
            exact add_mem (h₁ i) (h₂ i)
          · simp [TensorProduct.add_tmul, Finset.sum_add_distrib] }
    have hP : ∀ (e : EE) (n : N), ι e ∈ c.range → e ⊗ₜ[A] n ∈ P := by
      intro e n he
      obtain ⟨s, hs⟩ := (hN n).1 n.2
      have hn : n = ∑ i, a (s i) • (⟨x i, hxN i⟩ : N) := by
        apply Subtype.ext
        rw [hs]
        simp
      refine ⟨fun i => a (s i) • e, fun i => ?_, ?_⟩
      · beta_reduce
        rw [Algebra.smul_def, map_mul]
        exact mul_mem (ha (s i)) he
      · rw [hn, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul]
    intro t
    change t ∈ P
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add _ _ h₁ h₂ => exact add_mem h₁ h₂
    | tmul e n =>
      obtain ⟨e', he', hdec⟩ := ho e
      rw [hdec, TensorProduct.sum_tmul]
      refine sum_mem fun j _ => ?_
      rw [← algebraMap_smul A (o j) (e' j), TensorProduct.smul_tmul]
      exact hP _ _ (he' j)
  have hbij : Function.Bijective (N.subtype.liftBaseChange EE) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨e, he, rfl⟩ := hnf t
      choose w hw using he
      have h1 : ∑ i, e i • x i = 0 := by

        simpa [map_sum, LinearMap.liftBaseChange_tmul] using ht
      have h2 : (0 : Y) = ∑ i, c (w i) • jD (x i) := by
        simp only [hw]
        rw [← hjsum, h1, map_zero]
      have h3 : (0 : Y) = ∑ i, c ((0 : Fin (d * r) → W) i) • jD (x i) := by simp
      have h4 : w = 0 := (huniq 0).unique h2 h3
      have h5 : ∀ i, e i = 0 := by
        intro i
        apply hinj
        rw [← hw, h4]
        simp
      simp [h5]
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      intro y _
      refine Submodule.span_le.2 ?_ (hspan y)
      rintro _ ⟨i, rfl⟩
      exact ⟨1 ⊗ₜ[A] (⟨x i, hxN i⟩ : N), by simp [LinearMap.liftBaseChange_tmul]⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) fun n => ?_
  simp [LinearMap.liftBaseChange_tmul]

end GlobalTheory
end

section

open scoped LaurentSeries PowerSeries

namespace GlobalTheory.PsiBasis

variable {k : Type} [Field k]

noncomputable def comp (l : ℕ) (hl : 0 < l) (i : ℕ) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun y :=
    { coeff := fun m => y.coeff (l * m + i)
      isPWO_support' := by
        apply Set.IsWF.isPWO
        apply BddBelow.isWF
        refine ⟨min 0 (y.order - i), fun m hm => ?_⟩
        by_contra h
        apply hm
        apply HahnSeries.coeff_eq_zero_of_lt_order
        have h1 : m < 0 := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
        have h2 : m < y.order - i := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
        have h3 : (1 : ℤ) ≤ l := by exact_mod_cast hl
        nlinarith }
  map_add' x y := by ext m; simp
  map_smul' c x := by ext m; simp

theorem comp_coeff (l : ℕ) (hl : 0 < l) (i : ℕ) (y : k⸨X⸩) (m : ℤ) :
    (comp l hl i y).coeff m = y.coeff (l * m + i) := rfl

theorem p_zpow (s : ℤ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single s 1 := by
  cases s with
  | ofNat n => simp [HahnSeries.single_pow]
  | negSucc n =>
    rw [zpow_negSucc, HahnSeries.single_pow, HahnSeries.inv_single]
    simp [Int.negSucc_eq]

theorem p_pow (s : ℕ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single (s : ℤ) 1 := by
  simp [HahnSeries.single_pow]

theorem mem_iff (s : ℤ) (x : k⸨X⸩) :
    (∃ b : k⟦X⟧, x = (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s * (b : k⸨X⸩)) ↔
      ∀ m < s, x.coeff m = 0 := by
  rw [p_zpow]
  constructor
  · rintro ⟨b, rfl⟩ m hm
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, if_pos (by omega), mul_zero]
  · intro h
    refine ⟨PowerSeries.mk fun n => x.coeff (s + n), ?_⟩
    ext m
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, one_mul]
    split_ifs with hm
    · exact h m (by omega)
    · rw [PowerSeries.coeff_mk]; congr 1; omega

section
variable (l : ℕ) (hl : 0 < l) (φ : k⸨X⸩ →+* k⸨X⸩)
  (hφ : ∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0)
include hl hφ

theorem comp_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ j * φ a)
      = if j = i then a else 0 := by
  ext m
  have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [comp_coeff, p_pow, HahnSeries.coeff_single_mul, one_mul, hφ]
  by_cases h : j = i
  · subst h
    simp [Int.mul_ediv_cancel_left _ hl']
  · rw [if_neg h, if_neg]
    · simp
    · intro hd
      have : (l : ℤ) ∣ (i : ℤ) - j := by
        have h2 := dvd_sub hd (dvd_mul_right (l : ℤ) m)
        have e : (l : ℤ) * m + i - j - l * m = i - j := by ring
        rwa [e] at h2
      have := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega

theorem comp_one_add_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j * φ a)
      = (j.choose i) • a := by

  rw [add_comm, add_pow, Finset.sum_mul, map_sum]
  have : ∀ m ∈ Finset.range (j + 1),
      comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ m * 1 ^ (j - m) *
        (j.choose m : k⸨X⸩) * φ a) = if m = i then (j.choose i) • a else 0 := by
    intro m hm
    have hm' : m < l := by have := Finset.mem_range.1 hm; omega
    rw [one_pow, mul_one, mul_assoc, ← map_natCast φ, ← map_mul,
      comp_pow_mul l hl φ hφ hi hm']
    split_ifs with h
    · subst h; rw [nsmul_eq_mul]
    · rfl
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using h), zero_smul]

end

noncomputable def psi (l : ℕ) (hl : 0 < l) : k⸨X⸩ →ₗ[k] k⸨X⸩ :=
  ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i

theorem psi_apply (l : ℕ) (hl : 0 < l) (y : k⸨X⸩) :
    psi l hl y = ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i y := by
  simp only [psi, LinearMap.sum_apply, LinearMap.smul_apply]

end GlobalTheory.PsiBasis
end

section

namespace GlobalTheory.NonzeroScalarMembership

theorem exists_ne_zero_smul_mem {O LL V : Type} [CommRing O] [IsDomain O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V)
    (hT : Submodule.span LL (↑T : Set V) = ⊤) (x : V) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ T := by
  have hx : x ∈ Submodule.span LL (↑T : Set V) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem b hay
    · rw [mul_smul]
      exact T.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hq : (q : O) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨q * a, mul_ne_zero hq ha, ?_⟩
    have h : ((q : O) * a) • c • y = p • a • y := by
      have h1 : (q : O) • c • y = p • y := by
        rw [← algebraMap_smul LL (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
      rw [mul_comm, mul_smul, h1, smul_comm]
    rw [h]
    exact T.smul_mem p hay

end GlobalTheory.NonzeroScalarMembership
end

section

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem norm_scale_idem_add_compl {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A) (he : ψ e = 1)
    (hea : ∀ a, e * a = algebraMap K A (ψ a) * e) (c : K) :
    Algebra.norm K (algebraMap K A c * e + (1 - e)) = c := by
  classical
  let b := Module.Free.chooseBasis K A
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (Algebra.lmul K A (algebraMap K A c * e + (1 - e))) =
      1 + Matrix.replicateCol Unit (fun i => (c - 1) * b.repr e i) *
        Matrix.replicateRow Unit (fun j => ψ (b j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr ((algebraMap K A c * e + (1 - e)) * b j) i = _
    have h1 : (algebraMap K A c * e + (1 - e)) * b j = b j + ((c - 1) * ψ (b j)) • e := by
      have := hea (b j)
      rw [Algebra.smul_def, map_mul, map_sub, map_one]
      linear_combination (algebraMap K A c - 1) * this
    simp only [h1, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
    rw [Finsupp.single_apply]
    congr 1
    · split_ifs with h h' h' <;> first | rfl | (exfalso; exact h' h.symm) | (exfalso; exact h h'.symm)
    · ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : ∑ j, ψ (b j) * ((c - 1) * b.repr e j) = (c - 1) * ψ e := by
    conv_rhs => rw [← b.sum_repr e]

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]; ring
  rw [dotProduct, hs, he]; ring

theorem norm_eq_mul_norm_idem_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  intro K A _ _ _ _ ψ e he hea a
  have hee : e * e = e := by rw [hea e, he, map_one, one_mul]
  have hid : a = (e + (1 - e) * a) * (algebraMap K A (ψ a) * e + (1 - e)) := by
    have h1 := hea a
    linear_combination (-(algebraMap K A (ψ a) - algebraMap K A (ψ a) * a + a - 1)) * hee + h1
  conv_lhs => rw [hid]
  rw [map_mul, norm_scale_idem_add_compl ψ e he hea, mul_comm]

end GlobalTheory
end
