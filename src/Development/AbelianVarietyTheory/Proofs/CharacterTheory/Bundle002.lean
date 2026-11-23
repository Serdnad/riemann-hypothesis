module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.IntegralDomain

@[expose] public section

section

namespace GlobalTheory

theorem conj_mem_zpowers_of_mem_of_pRegular {G : Type} [Group G] (c : G) (p : ℕ) (H : Subgroup G)
    (hc : Nat.Coprime (orderOf c) p)
    (hp : ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) (g : G)
    (hg : g⁻¹ * c * g ∈ H) : g⁻¹ * c * g ∈ Subgroup.zpowers c := by
  obtain ⟨k, hk⟩ := hp _ hg
  have ho : orderOf (g⁻¹ * c * g) = orderOf c := by
    have := (MulAut.conj g⁻¹).orderOf_eq c
    simpa using this
  have hcop : Nat.Coprime (p ^ k) (orderOf (g⁻¹ * c * g)) := by
    rw [ho]
    exact Nat.Coprime.pow_left k hc.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hk m

theorem card_fixedBy_quotient_eq_relIndex_of_pRegular :
    ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  intro G _ _ c p H N hc hH hp hN
  have key : ∀ g : G, c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g ∈ N := by
    intro g
    have h1 : c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g⁻¹ * c * g ∈ H := by
      rw [eq_comm, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_assoc]
    rw [h1]
    constructor
    · intro hg
      have hy := conj_mem_zpowers_of_mem_of_pRegular c p H hc hp g hg
      rw [← N.inv_mem_iff, hN]
      rintro d ⟨n, rfl⟩
      have h2 := Subgroup.zpow_mem _ hy n
      have h3 : (g⁻¹ * c * g) ^ n = g⁻¹ * c ^ n * g⁻¹⁻¹ := by
        rw [← conj_zpow, inv_inv]
      rw [h3] at h2
      exact h2
    · intro hg
      have := (hN _).1 (N.inv_mem hg) c (Subgroup.mem_zpowers c)
      rw [inv_inv] at this
      exact hH this
  let f : N ⧸ H.subgroupOf N → MulAction.fixedBy (G ⧸ H) c :=
    Quotient.lift (fun n : N => ⟨((n : G) : G ⧸ H), (key n).2 n.2⟩) (by
      intro a b hab
      apply Subtype.ext
      have h : a⁻¹ * b ∈ H.subgroupOf N := QuotientGroup.leftRel_apply.1 hab
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using h))
  have hf : Function.Bijective f := by
    constructor
    · intro x y
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      intro hab
      have h : ((a : G) : G ⧸ H) = ((b : G) : G ⧸ H) := congrArg Subtype.val hab
      rw [QuotientGroup.eq] at h ⊢
      simpa [Subgroup.mem_subgroupOf] using h
    · rintro ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with
      | H g => exact ⟨((⟨g, (key g).1 hx⟩ : N) : N ⧸ H.subgroupOf N), rfl⟩
  exact (Nat.card_eq_of_bijective f hf).symm

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_coprime_orderOf_pow_prime_pow (G : Type) [Group G] [Finite G] (x : G) (p : ℕ)
    (hp : p.Prime) : ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  obtain ⟨k, u, hu, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  have h1 : orderOf (x ^ p ^ k) ∣ u := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← h, pow_orderOf_eq_one]
  exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm

end GlobalTheory
end

section

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

theorem exists_rat_eq_transpose_mul_diagonal_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hs : A.IsSymm) (hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) :
    ∃ (d : Fin n → ℚ) (Q : Matrix (Fin n) (Fin n) ℚ), (∀ i, 0 < d i) ∧ Q.det ≠ 0 ∧
      A = Qᵀ * Matrix.diagonal d * Q := by
  have hsym : (Matrix.toBilin' A).IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := Fin n → ℚ)
    (B := Matrix.toBilin' A) (LinearMap.BilinForm.isSymm_iff.mp hsym)
  have hr : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr hr
  let v := v₀.reindex e
  have hv : ∀ i j, i ≠ j → v i ⬝ᵥ A *ᵥ v j = 0 := by
    intro i j hij
    have h := hv₀ (e.symm.injective.ne hij)
    simp only [Function.onFun] at h
    rw [Matrix.toBilin'_apply'] at h
    simpa only [v, Module.Basis.reindex_apply] using h
  let P : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => v i j
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp v.linearIndependent
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdiag : P * A * Pᵀ = Matrix.diagonal fun i => v i ⬝ᵥ A *ᵥ v i := by
    ext i j
    have : (P * A * Pᵀ) i j = v i ⬝ᵥ A *ᵥ v j := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, P, dotProduct, Matrix.mulVec]
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hv i j hij]
  refine ⟨fun i => v i ⬝ᵥ A *ᵥ v i, (P⁻¹)ᵀ, fun i => hp _ (v.ne_zero i), ?_, ?_⟩
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det P hPd).ne_zero
  · rw [← hdiag, Matrix.transpose_transpose]
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
    have h2 : Pᵀ * (P⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc A = (P⁻¹ * P) * A * (Pᵀ * (P⁻¹)ᵀ) := by rw [h1, h2]; simp
      _ = P⁻¹ * (P * A * Pᵀ) * (P⁻¹)ᵀ := by simp only [Matrix.mul_assoc]

theorem exists_pos_nat_mul_eq_intCast {ι : Type} [Finite ι] (f : ι → ℚ) :
    ∃ (b : ℕ) (g : ι → ℤ), 0 < b ∧ ∀ i, (g i : ℚ) = b * f i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose g hg using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  refine ⟨((b : ℤ) * b).toNat, fun i => b * g i, ?_, fun i => ?_⟩
  · have := mul_self_pos.mpr hb0
    omega
  · have h1 : ((((b : ℤ) * b).toNat : ℕ) : ℤ) = b * b := Int.toNat_of_nonneg (mul_self_nonneg _)
    have h2 : ((((b : ℤ) * b).toNat : ℕ) : ℚ) = ((b : ℤ) : ℚ) * (b : ℤ) := by exact_mod_cast h1
    have h3 : (g i : ℚ) = ((b : ℤ) : ℚ) * f i := by
      have := hg i
      simpa [zsmul_eq_mul] using this
    rw [h2]
    push_cast
    rw [h3]
    ring

theorem exists_smul_eq_transpose_mul_diagonal_mul :
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), (A.map (fun x : ℤ => (x : ℝ))).PosDef → ∃ (N : ℕ) (c : Fin n → ℕ) (l : Matrix (Fin n) (Fin n) ℤ), 0 < N ∧ (∀ i, 0 < c i) ∧ l.det ≠ 0 ∧ (N : ℤ) • A = lᵀ * Matrix.diagonal (fun i => (c i : ℤ)) * l) := by
  intro n A hA
  have hs : (A.map (fun x : ℤ => (x : ℚ))).IsSymm := by
    ext i j
    have := hA.isHermitian.apply j i
    simp only [Matrix.map_apply, star_trivial, Int.cast_inj] at this
    simp [this]
  have hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x := by
    intro x hx
    have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
      intro h
      apply hx
      ext i
      have := congrFun h i
      simpa using this
    have h := hA.dotProduct_mulVec_pos hx'
    have h2 : star (fun i => (x i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (x i : ℝ))
        = ((x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x : ℚ) : ℝ) := by
      simp [dotProduct, Matrix.mulVec]
    rw [h2] at h
    exact_mod_cast h
  obtain ⟨d, Q, hd, hQ, hAQ⟩ := exists_rat_eq_transpose_mul_diagonal_mul _ hs hp
  obtain ⟨a, g, ha, hg⟩ := exists_pos_nat_mul_eq_intCast (fun p : Fin n × Fin n => Q p.1 p.2)
  obtain ⟨b, k, hb, hk⟩ := exists_pos_nat_mul_eq_intCast d
  have hkpos : ∀ i, 0 < k i := by
    intro i
    have : (0 : ℚ) < k i := by
      rw [hk i]
      exact mul_pos (by exact_mod_cast hb) (hd i)
    exact_mod_cast this
  let l : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => g (i, j)
  have hl : l.map (Int.castRingHom ℚ) = (a : ℚ) • Q := by
    ext i j
    simp [l, hg]
  have hc : (Matrix.diagonal fun i => (((k i).toNat : ℕ) : ℤ)).map (Int.castRingHom ℚ)
      = (b : ℚ) • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rw [Int.toNat_of_nonneg (hkpos i).le]
      exact hk i
    · simp [Matrix.diagonal_apply_ne _ hij]
  refine ⟨a * b * a, fun i => (k i).toNat, l, by positivity, fun i => ?_, ?_, ?_⟩
  · have := hkpos i
    show 0 < (k i).toNat
    omega
  · intro h0
    have h1 : (l.map (Int.castRingHom ℚ)).det = 0 := by
      have := (Int.castRingHom ℚ).map_det l
      rw [RingHom.mapMatrix_apply, h0] at this
      simpa using this.symm
    rw [hl, Matrix.det_smul] at h1
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    exact (mul_ne_zero (pow_ne_zero _ ha') hQ) h1
  · apply Matrix.map_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hl, hc]
    have : (((a * b * a : ℕ) : ℤ) • A).map (Int.castRingHom ℚ)
        = ((a : ℚ) * b * a) • A.map (fun x : ℤ => (x : ℚ)) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      push_cast
      ring
    rw [this, hAQ]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
end

section

namespace GlobalTheory

theorem trace_eq_add_of_shortExact (K : Type) [Field K]
    (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p)
    (hb : b ∘ₗ i = i ∘ₗ a) (hc : p ∘ₗ b = c ∘ₗ p) :
    LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  obtain ⟨r₀, hr₀⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hs' : ∀ w, p (s w) = w := fun w => LinearMap.congr_fun hs w
  have hr' : ∀ u, r₀ (i u) = u := fun u => LinearMap.congr_fun hr₀ u
  have hpi : ∀ u, p (i u) = 0 := fun u => by
    have : i u ∈ LinearMap.ker p := hex ▸ LinearMap.mem_range_self i u
    exact this
  have hb' : ∀ u, b (i u) = i (a u) := fun u => LinearMap.congr_fun hb u
  have hc' : ∀ v, p (b v) = c (p v) := fun v => LinearMap.congr_fun hc v
  let r : V →ₗ[K] U := r₀ ∘ₗ (LinearMap.id - s ∘ₗ p)
  have hri : ∀ u, r (i u) = u := fun u => by
    simp [r, hpi, hr']
  have hir : ∀ v, i (r v) = v - s (p v) := fun v => by
    have : v - s (p v) ∈ LinearMap.range i := by
      rw [hex, LinearMap.mem_ker, map_sub, hs', sub_self]
    obtain ⟨u, hu⟩ := this
    have h2 : r v = u := by
      show r₀ (v - s (p v)) = u
      rw [← hu, hr']
    rw [h2, hu]
  have hdec : b = (b ∘ₗ i) ∘ₗ r + (b ∘ₗ s) ∘ₗ p := by
    ext v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hir, map_sub, sub_add_cancel]
  have h1 : r ∘ₗ (b ∘ₗ i) = a := by
    ext u
    simp only [LinearMap.comp_apply, hb', hri]
  have h2 : p ∘ₗ (b ∘ₗ s) = c := by
    ext w
    simp only [LinearMap.comp_apply, hc', hs']
  calc LinearMap.trace K V b
      = LinearMap.trace K V ((b ∘ₗ i) ∘ₗ r) + LinearMap.trace K V ((b ∘ₗ s) ∘ₗ p) := by
        rw [← map_add (f := _), ← hdec]
    _ = LinearMap.trace K U a + LinearMap.trace K W c := by
        rw [LinearMap.trace_comp_comm' r (b ∘ₗ i), LinearMap.trace_comp_comm' p (b ∘ₗ s), h1, h2]

end GlobalTheory
end

section

namespace GlobalTheory


open Finset in
theorem exists_weight_idempotent (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G)
    (lam : B →* Lˣ) (v : V) (hB : B.Normal) (hv : v ≠ 0)
    (hlam : ∀ b : B, ρ b v = (lam b : L) • v)
    (hT : ∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) :
    ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧
      (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  have hc : (Fintype.card B : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set s : Module.End L V := ∑ b : B, (((lam b)⁻¹ : Lˣ) : L) • ρ b with hs
  set e : Module.End L V := (Fintype.card B : L)⁻¹ • s with he
  have h1 : ∀ b : B, ρ b * s = (lam b : L) • s := by
    intro b
    rw [hs, Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
    intro c
    simp only [Equiv.coe_mulLeft, map_mul, Subgroup.coe_mul, smul_smul, mul_smul_comm]
    congr 1
    simp [mul_comm]
  have h1e : ∀ b : B, ρ b * e = (lam b : L) • e := by
    intro b
    rw [he, mul_smul_comm, h1, smul_comm]
  have h2 : ∀ f : Module.End L V, (∀ b : B, ρ b * f = (lam b : L) • f) → e * f = f := by
    intro f hf
    rw [he, smul_mul_assoc, hs, Finset.sum_mul]
    have : ∀ b : B, ((((lam b)⁻¹ : Lˣ) : L) • ρ b) * f = f := by
      intro b
      rw [smul_mul_assoc, hf, smul_smul]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hev : e v = v := by
    rw [he, hs]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, hlam, smul_smul, Units.inv_mul, one_smul,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let κ : G → B ≃* B := fun g => (MulAut.conjNormal (H := B) g⁻¹)
  have hκ : ∀ g (b : B), (κ g b : G) = g⁻¹ * b * g := by
    intro g b
    simp [κ]
  have hcomm : ∀ g (b : B), ρ b * ρ g = ρ g * ρ (κ g b) := by
    intro g b
    rw [← map_mul, ← map_mul, hκ]
    congr 1
    group
  refine ⟨e, ?_, h2 e h1e, h1e, ?_, ?_⟩
  · intro h
    rw [h] at hev
    exact hv hev.symm
  · intro t ht
    have ht' := (hT t).1 ht
    rw [he, mul_smul_comm, smul_mul_assoc, hs, Finset.mul_sum, Finset.sum_mul]
    congr 1
    symm
    refine Fintype.sum_equiv (κ t).toEquiv _ _ ?_
    intro b
    have := ht' b (κ t b) (hκ t b)
    rw [smul_mul_assoc, mul_smul_comm, hcomm, ← this]
    rfl
  · intro g hg
    let f : B →* L := (Units.coeHom L).comp (lam⁻¹ * lam.comp (κ g).toMonoidHom)
    have hf : f ≠ 1 := by
      intro h
      apply hg
      rw [hT]
      intro b b' hb
      have hb' : b' = κ g b := Subtype.ext (by rw [hb, hκ])
      have h3 : f b = 1 := by rw [h]; rfl
      have h4 : (lam b)⁻¹ * lam (κ g b) = 1 := Units.ext h3
      rw [hb']
      exact (inv_mul_eq_one.mp h4).symm
    have h0 := sum_hom_units_eq_zero f hf
    have : s * ρ g * e = 0 := by
      rw [hs, Finset.sum_mul, Finset.sum_mul]
      have : ∀ b : B, ((((lam b)⁻¹ : Lˣ) : L) • ρ b) * ρ g * e = f b • (ρ g * e) := by
        intro b
        rw [smul_mul_assoc, smul_mul_assoc, hcomm, mul_assoc, h1e, mul_smul_comm, smul_smul]
        rfl
      simp only [this]
      rw [← Finset.sum_smul, h0, zero_smul]
    calc e * ρ g * e = (Fintype.card B : L)⁻¹ • (s * ρ g * e) := by
          rw [← smul_mul_assoc, ← smul_mul_assoc]
      _ = 0 := by rw [this, smul_zero]

end GlobalTheory
end

section

namespace GlobalTheory

theorem irreducible_idempotent_eq_one_and_character_eq_weight
    (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (ρ : Representation L G V) (hρ : ρ.IsIrreducible) :
    (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧
    (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) →
      ∀ g, ρ.character g = (lam g : L)) := by
  have key : ∀ (W : Submodule L V), (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW hne
    let S : Subrepresentation ρ := ⟨W, fun g x hx => hW g x hx⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hne
    · exact congrArg Subrepresentation.toSubmodule h
  refine ⟨fun e he hee hc => ?_, fun lam v hv hl g => ?_⟩
  · have h : LinearMap.range e = ⊤ := by
      refine key _ ?_ ?_
      · rintro g _ ⟨u, rfl⟩
        exact ⟨ρ g u, (congrArg (fun f : Module.End L V => f u) (hc g)).symm⟩
      · intro h
        exact he (LinearMap.range_eq_bot.mp h)
    ext w
    obtain ⟨u, rfl⟩ := LinearMap.range_eq_top.mp h w
    exact congrArg (fun f : Module.End L V => f u) hee
  · have h : Submodule.span L {v} = ⊤ := by
      refine key _ ?_ ?_
      · intro g x hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hl]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      · simpa using hv
    have hfin : Module.finrank L V = 1 := by
      rw [← finrank_top, ← h]
      exact finrank_span_singleton hv
    have hg : ρ g = (lam g : L) • LinearMap.id := by
      ext x
      have hx : x ∈ Submodule.span L {v} := h ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hl, smul_comm c]
    simp [Representation.character, hg, hfin]

end GlobalTheory
end
