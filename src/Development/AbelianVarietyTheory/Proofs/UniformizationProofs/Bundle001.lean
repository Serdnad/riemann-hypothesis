module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

section

namespace GlobalTheory

theorem shortest_vector_strict_of_mul :
    ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (n r : ℕ), 1 ≤ n → 2 ≤ r → ∀ z : X, (∀ m, Q z ≤ Q (z + n • m)) → ∀ m : X, (n * r) • m ≠ 0 → Q z < Q (z + (n * r) • m) := by
  intro X _ Q B hadd hdiag hpos n r _ hr z hmin m hm
  have hnr : (n * r) • m = r • (n • m) := by rw [mul_comm, mul_smul]
  rw [hnr] at hm ⊢
  have h1 := hmin m
  generalize n • m = a at hm h1
  have ha : a ≠ 0 := by
    rintro rfl
    exact hm (smul_zero _)
  have hQa := hpos a ha
  have h2 : 2 * Q (r • a) = (r : ℤ) * ((r : ℤ) * (2 * Q a)) := by
    rw [hdiag, hdiag]
    simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  have h3 : B z (r • a) = (r : ℤ) * B z a := by
    simp only [map_nsmul, nsmul_eq_mul]
  rw [hadd] at h1 ⊢
  rw [h3]
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have h4 : 0 ≤ (r : ℤ) * (Q a + B z a) := mul_nonneg (by omega) (by omega)
  have h5 : 0 < ((r : ℤ) * (r - 1)) * Q a :=
    mul_pos (mul_pos (by omega) (by omega)) (by omega)
  nlinarith

end GlobalTheory
end

section

namespace GlobalTheory.UU

theorem le_of_pow_le_poly_mul_pow (A B K a g : ℕ)
    (H : ∀ k, A ^ k ≤ K * B ^ k * (1 + k * a) ^ g) : A ≤ B := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · have := H 1
    simp [hB] at this
    omega
  by_contra hAB
  push Not at hAB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : (1 : ℝ) < (A : ℝ) / B := by
    rw [one_lt_div hBr]; exact_mod_cast hAB
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt g hr).const_mul
    ((K : ℝ) * (1 + a) ^ g)
  rw [mul_zero] at ht
  have h1 : ∀ᶠ k : ℕ in Filter.atTop,
      (1 : ℝ) ≤ ((K : ℝ) * (1 + a) ^ g) * ((k : ℝ) ^ g / ((A : ℝ) / B) ^ k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk' : A ^ k ≤ K * B ^ k * ((1 + a) * k) ^ g := by
      refine (H k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      nlinarith
    have hk2 : (A : ℝ) ^ k ≤ K * (B : ℝ) ^ k * ((1 + a) * k) ^ g := by exact_mod_cast hk'
    have hA : (0 : ℝ) < A := by exact_mod_cast (hB.trans hAB)
    rw [div_pow, ← mul_div_assoc, div_div_eq_mul_div, one_le_div (by positivity)]
    refine hk2.trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have := ge_of_tendsto ht h1
  linarith

theorem degree_eq_pow_of_growth :
    ∀ (h : ℕ → ℕ) (g c C a d q : ℕ), 1 ≤ c → 1 ≤ q → (∀ t t', t ≤ t' → h t ≤ h t') → (∀ t, 1 ≤ t → t ^ g ≤ c * h t ∧ h t ≤ C * t ^ g) → (∀ t, d * h t ≤ h (q * (t + a)) ∧ h (q * t) ≤ d * h (t + a)) → d = q ^ g := by
  intro h g c C a d q hc hq hm hg hd
  have h1 : 1 ≤ h 1 := by
    have := (hg 1 le_rfl).1
    rcases Nat.eq_zero_or_pos (h 1) with h0 | h0
    · simp [h0] at this
    · exact h0
  have up : ∀ k t, h (q ^ k * t) ≤ d ^ k * h (t + k * a) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have e1 : q ^ (k + 1) * t = q ^ k * (q * t) := by ring
      rw [e1]
      refine (ih _).trans ?_
      rw [pow_succ, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have e2 : t + (k + 1) * a = t + k * a + a := by ring
      rw [e2]
      refine le_trans (hm _ _ ?_) (hd (t + k * a)).2
      rw [mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hq) _
  have lo : ∀ k, d ^ k ≤ h (q ^ k * (1 + k * a)) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ, mul_comm]
      refine (Nat.mul_le_mul_left d ih).trans ((hd _).1.trans (hm _ _ ?_))
      have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
      have e : q ^ (k + 1) * (1 + (k + 1) * a) = q * (q ^ k * (1 + k * a) + q ^ k * a) := by ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hp) _)
  apply le_antisymm
  · apply le_of_pow_le_poly_mul_pow d (q ^ g) C a g
    intro k
    have hp : 1 ≤ q ^ k * (1 + k * a) := Nat.mul_pos (Nat.pow_pos hq) (by omega)
    refine (lo k).trans ((hg _ hp).2.trans (le_of_eq ?_))
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k g]; ring
  · apply le_of_pow_le_poly_mul_pow (q ^ g) d (c * C) a g
    intro k
    have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have a1 := (hg _ hp).1
    have a2 := up k 1
    rw [mul_one] at a2
    have a3 := (hg (1 + k * a) (by omega)).2
    calc (q ^ g) ^ k = (q ^ k) ^ g := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ c * h (q ^ k) := a1
      _ ≤ c * (d ^ k * (C * (1 + k * a) ^ g)) :=
        Nat.mul_le_mul_left _ (a2.trans (Nat.mul_le_mul_left _ a3))
      _ = _ := by ring

end GlobalTheory.UU
end

section

set_option autoImplicit false

open AddMonoidAlgebra

namespace GlobalTheory.MulCocycle

theorem finsupp_homotopy {X : Type*} [Zero X] {N : Type*} [AddCommGroup N] (f : X × X →₀ N)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) (q : X × X) :
    (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) =
      (f - (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
        g.mapDomain (fun y => (y, (0 : X)))) : X × X →₀ N) q := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  obtain rfl : g = s f := Finsupp.ext hg
  clear hg
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← sub_eq_zero] at hf hg ⊢
    rw [← add_zero (0 : N)]
    nth_rewrite 1 [← hf]
    rw [← hg]; abel
  | single p m =>
    obtain ⟨y, z⟩ := p
    by_cases h : y = 0
    · subst h
      have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
        ext x; simp [hs, Finsupp.single_apply]
      simp [this, Finsupp.single_apply]
      abel
    · have : s (Finsupp.single (y, z) m) = 0 := by
        ext x; simp [hs, h]
      simp [this, Finsupp.single_apply, h]

variable {B : Type*} [CommRing B] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

theorem mem_map_algebraMap_iff (J : Ideal B) (b : B[X]) :
    b ∈ J.map (algebraMap B B[X]) ↔ ∀ x, b.coeff x ∈ J := by
  constructor
  · intro hb
    have hb' : b ∈ J • (⊤ : Submodule B B[X]) := by
      rw [Ideal.smul_top_eq_map]; exact hb
    refine Submodule.smul_induction_on hb' (p := fun b => ∀ x, b.coeff x ∈ J) ?_ ?_
    · intro r hr m _ x
      simpa using J.mul_mem_right _ hr
    · intro m m' h h' x
      simpa using J.add_mem (h x) (h' x)
  · intro h
    rw [← AddMonoidAlgebra.sum_coeff_single b]
    refine Ideal.sum_mem _ fun x _ => ?_
    have : single x (b.coeff x) = single x 1 * algebraMap B B[X] (b.coeff x) := by
      simp [AddMonoidAlgebra.single_mul_single]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h x))

theorem algHom_mem_map {C C' : Type*} [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
    {J : Ideal B} (φ : C →ₐ[B] C') {a : C} (ha : a ∈ J.map (algebraMap B C)) :
    φ a ∈ J.map (algebraMap B C') := by
  have := Ideal.mem_map_of_mem (φ : C →+* C') ha
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem mul_mem_map_sq {C : Type*} [CommRing C] [Algebra B C] {J : Ideal B} {a b : C}
    (ha : a ∈ J.map (algebraMap B C)) (hb : b ∈ J.map (algebraMap B C)) :
    a * b ∈ (J ^ 2).map (algebraMap B C) := by
  rw [Ideal.map_pow, pow_two]
  exact Ideal.mul_mem_mul ha hb

theorem exists_unit_of_faces {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [Algebra B R₁] [Algebra B R₂] [Algebra B R₃]
    (e₀ e₁ e₂ : R₁ →ₐ[B] R₂) (d₀ d₁ d₂ d₃ : R₂ →ₐ[B] R₃)
    (h₁ : ∀ w, d₁ (e₁ w) = d₂ (e₁ w)) (h₂ : ∀ w, d₁ (e₂ w) = d₃ (e₁ w))
    (h₃ : ∀ w, d₁ (e₀ w) = d₀ (e₀ w)) (h₄ : ∀ w, d₃ (e₂ w) = d₂ (e₂ w))
    (h₅ : ∀ w, d₃ (e₀ w) = d₀ (e₂ w)) (h₆ : ∀ w, d₂ (e₀ w) = d₀ (e₁ w))
    (H : ∀ (K L : Ideal B) (φ : R₂), φ ∈ K.map (algebraMap B R₂) →
      d₀ φ - d₁ φ + d₂ φ - d₃ φ ∈ L.map (algebraMap B R₃) →
      ∃ ψ ∈ K.map (algebraMap B R₁), φ - (e₀ ψ - e₁ ψ + e₂ ψ) ∈ L.map (algebraMap B R₂))
    (n : ℕ) : ∀ (K : Ideal B), K ^ 2 ^ n = ⊥ → ∀ f : R₂, f - 1 ∈ K.map (algebraMap B R₂) →
      d₁ f * d₃ f = d₂ f * d₀ f →
      ∃ g : R₁ˣ, g.val - 1 ∈ K.map (algebraMap B R₁) ∧ f * e₁ g.val = e₂ g.val * e₀ g.val := by
  induction n with
  | zero =>
    intro K hK f hf _
    rw [pow_zero, pow_one] at hK
    rw [hK, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero] at hf
    exact ⟨1, by simp, by simp [hf]⟩
  | succ n ih =>
    intro K hK f hf hc
    obtain ⟨φ, rfl⟩ : ∃ φ, f = 1 + φ := ⟨f - 1, by ring⟩
    rw [add_sub_cancel_left] at hf
    have hc' := hc
    simp only [map_add (f := _), map_one] at hc'
    obtain ⟨ψ, hψ, e⟩ := H K (K ^ 2) φ hf (by
      have : d₀ φ - d₁ φ + d₂ φ - d₃ φ = d₁ φ * d₃ φ - d₂ φ * d₀ φ := by
        linear_combination -hc'
      rw [this]
      exact sub_mem (mul_mem_map_sq (algHom_mem_map _ hf) (algHom_mem_map _ hf))
        (mul_mem_map_sq (algHom_mem_map _ hf) (algHom_mem_map _ hf)))
    have hn : IsNilpotent ψ := ⟨2 ^ (n + 1), by
      have := Ideal.pow_mem_pow hψ (2 ^ (n + 1))
      rwa [← Ideal.map_pow, hK, Ideal.map_bot, Ideal.mem_bot] at this⟩
    obtain ⟨u, hu⟩ := hn.isUnit_one_add
    have huv : u.val * (u⁻¹).val = 1 := u.mul_inv
    generalize (u⁻¹).val = v at huv
    have k (e : R₁ →ₐ[B] R₂) : e u.val * e v = 1 := by rw [← map_mul, huv, map_one]
    have k' (d : R₂ →ₐ[B] R₃) (e : R₁ →ₐ[B] R₂) : d (e u.val) * d (e v) = 1 := by
      rw [← map_mul, k, map_one]
    obtain ⟨g, hg, hg'⟩ := ih (K ^ 2) (by rw [← pow_mul, ← pow_succ', hK])
      ((1 + φ) * e₁ u.val * e₂ v * e₀ v) (by
        have : (1 + φ) * e₁ u.val * e₂ v * e₀ v - 1 =
            ((φ - (e₀ ψ - e₁ ψ + e₂ ψ)) + φ * e₁ ψ - e₂ ψ * e₀ ψ) * (e₂ v * e₀ v) := by
          have k₀ := k e₀
          have k₂ := k e₂
          rw [hu] at k₀ k₂ ⊢
          simp only [map_add (f := _), map_one] at k₀ k₂ ⊢
          linear_combination ((1 + e₀ ψ) * e₀ v) * k₂ + k₀
        rw [this]
        exact Ideal.mul_mem_right _ _ (sub_mem (add_mem e
          (mul_mem_map_sq hf (algHom_mem_map _ hψ)))
          (mul_mem_map_sq (algHom_mem_map _ hψ) (algHom_mem_map _ hψ)))) (by
        have k₁ := k' d₃ e₁
        have k₂ := k' d₀ e₁
        generalize 1 + φ = f at hc
        simp only [map_mul, h₁, h₂, h₃, h₄, h₅, h₆]
        linear_combination
          (d₂ (e₁ u.val) * d₂ (e₂ v) * d₀ (e₂ v) * d₀ (e₀ v)) *
            (d₁ f * d₃ f * k₁ - d₂ f * d₀ f * k₂ + hc))
    refine ⟨u * g, ?_, ?_⟩
    · have : (u * g).val - 1 = u.val * (g.val - 1) + ψ := by
        rw [Units.val_mul, hu]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _
        (Ideal.map_mono (Ideal.pow_le_self two_ne_zero) hg)) hψ
    · have k₀ := k e₀
      have k₂ := k e₂
      simp only [Units.val_mul, map_mul]
      linear_combination (e₂ u.val * e₀ u.val) * hg' -
        ((1 + φ) * e₁ u.val * e₁ g.val) * (e₀ u.val * e₀ v * k₂ + k₀)

end GlobalTheory.MulCocycle

namespace GlobalTheory

open MulCocycle

theorem exists_unit_coboundary_of_mul_cocycle (B : Type) [CommRing B] (I : Ideal B)
    (hI : IsNilpotent I) (X : Type) [AddCommGroup X] (f : AddMonoidAlgebra B (X × X))
    (hf : ∀ p, (f - 1).coeff p ∈ I)
    (hc : AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) f *
        AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) f =
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) f *
        AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) f) :
    ∃ g : (AddMonoidAlgebra B X)ˣ, (∀ x, (g.val - 1).coeff x ∈ I) ∧
      f * AddMonoidAlgebra.mapDomain (fun x : X => (x, x)) g.val =
        AddMonoidAlgebra.mapDomain (fun x : X => (x, (0 : X))) g.val *
          AddMonoidAlgebra.mapDomain (fun x : X => ((0 : X), x)) g.val := by
  obtain ⟨n, hn⟩ := hI
  have hn' : I ^ 2 ^ n = ⊥ :=
    le_bot_iff.1 ((Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le).trans hn.le)
  have key : ∀ (a a' : X →+ X × X) (b b' : X × X →+ X × X × X), (∀ x, b (a x) = b' (a' x)) →
      ∀ w : B[X], mapDomainAlgHom B B b (mapDomainAlgHom B B a w) =
        mapDomainAlgHom B B b' (mapDomainAlgHom B B a' w) := by
    intro a a' b b' h w
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | single x r => simp [h]
  obtain ⟨g, hg, hg'⟩ := exists_unit_of_faces (B := B)
    (mapDomainAlgHom B B (AddMonoidHom.inr X X))
    (mapDomainAlgHom B B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)))
    (mapDomainAlgHom B B (AddMonoidHom.inl X X))
    (mapDomainAlgHom B B (AddMonoidHom.inr X (X × X)))
    (mapDomainAlgHom B B ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))))
    (mapDomainAlgHom B B ((AddMonoidHom.fst X X).prod
      ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))))
    (mapDomainAlgHom B B ((AddMonoidHom.id X).prodMap (AddMonoidHom.inl X X)))
    (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl)
    (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl)
    (fun K L φ hφ hd => by
      rw [mem_map_algebraMap_iff] at hφ hd
      refine ⟨ofCoeff (φ.coeff.comapDomain (fun x => ((0 : X), x))
        (Prod.mk_right_injective 0).injOn), (mem_map_algebraMap_iff _ _).2 fun x => hφ (0, x),
        (mem_map_algebraMap_iff _ _).2 fun q => ?_⟩
      have := finsupp_homotopy φ.coeff (φ.coeff.comapDomain (fun x => ((0 : X), x))
        (Prod.mk_right_injective 0).injOn) (fun _ => rfl) q
      exact (congrArg (· ∈ L) this).mp (hd (0, q)))
    n I hn' f ((mem_map_algebraMap_iff _ _).2 hf) hc
  exact ⟨g, (mem_map_algebraMap_iff _ _).1 hg, hg'⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FiniteSeparablePoints

theorem exists_factor_of_unramified {k Ω S : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing S]
    [Algebra k S] [Algebra.FormallyUnramified k S] [Algebra.FiniteType k S] (φ : S →ₐ[k] Ω) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ ψ : S →+* K, (algebraMap K Ω).comp ψ = φ.toRingHom := by
  classical
  let R : Subalgebra k Ω := φ.range
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have : Algebra.FiniteType k R := Algebra.FiniteType.of_surjective φ.rangeRestrict hsurj
  have : Algebra.FormallyUnramified k R := Algebra.FormallyUnramified.of_surjective φ.rangeRestrict hsurj
  have : Module.Finite k R := Algebra.FormallyUnramified.finite_of_free k R
  have hF : IsField R := isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)
  let K : IntermediateField k Ω := R.toIntermediateField' hF
  have hmem : ∀ x, φ x ∈ K.toSubalgebra := fun x => ⟨x, rfl⟩
  let ψ : S →ₐ[k] K := φ.codRestrict K.toSubalgebra hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have : Algebra.FiniteType k K := Algebra.FiniteType.of_surjective ψ hψ
  have : Algebra.FormallyUnramified k K := Algebra.FormallyUnramified.of_surjective ψ hψ
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  refine ⟨K, inferInstance, (Algebra.FormallyUnramified.iff_isSeparable k K).1 inferInstance,
    ψ.toRingHom, ?_⟩
  ext x
  rfl

theorem exists_finite_separable_point {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p]
    [LocallyOfFiniteType p] (a : Spec (CommRingCat.of Ω) ⟶ X)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  classical
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨_, ⟨U, hU0, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a pt)) isOpen_univ
  have hU : IsAffineOpen U := hU0
  have hrange : Set.range a ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y pt]
  have hca : IsOpenImmersion.lift hU.fromSpec a hrange ≫ hU.fromSpec = a :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f = IsOpenImmersion.lift hU.fromSpec a hrange :=
    ⟨_, Spec.map_preimage _⟩
  obtain ⟨g, hg⟩ : ∃ g, Spec.map g = hU.fromSpec ≫ p := ⟨_, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap k Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, hg, ← Category.assoc, hca, h]
  have hU1 : RingHom.FormallyUnramified g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @FormallyUnramified), hg]
    exact HasRingHomProperty.comp_of_isOpenImmersion @FormallyUnramified hU.fromSpec p ‹_›
  have hU2 : RingHom.FiniteType g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hg]
    infer_instance
  let _ : Algebra k Γ(X, U) := g.hom.toAlgebra
  have : Algebra.FormallyUnramified k Γ(X, U) := hU1
  have : Algebra.FiniteType k Γ(X, U) := hU2
  let φ' : Γ(X, U) →ₐ[k] Ω :=
    { f.hom with
      commutes' := fun r => by
        have e := congrArg (fun q => q.hom r) hgf
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
        exact e }
  obtain ⟨K, hK1, hK2, ψ, hψ⟩ := exists_factor_of_unramified φ'
  refine ⟨K, hK1, hK2, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  have e : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K Ω) = f := by
    ext x
    exact congrArg (fun q => q x) hψ
  rw [← Category.assoc, ← Spec.map_comp, e, hf, hca]

end GlobalTheory.FiniteSeparablePoints
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.Unif

theorem locallyQuasiFinite_of_isPullback_surjective :
    ∀ (X Z X' Z' : Scheme.{0}) (φ : X ⟶ Z) (φ' : X' ⟶ Z') (a : X' ⟶ X) (p : Z' ⟶ Z),
      IsPullback a φ' φ p → Surjective p → LocallyOfFiniteType φ → QuasiCompact φ →
      LocallyQuasiFinite φ' → LocallyQuasiFinite φ := by
  intro X Z X' Z' φ φ' a p h hp _ hqc _
  have : QuasiCompact φ' := MorphismProperty.of_isPullback h hqc
  refine LocallyQuasiFinite.of_finite_preimage_singleton φ fun z => ?_
  obtain ⟨z', rfl⟩ := p.surjective z
  refine ((φ'.finite_preimage_singleton z').image a).subset fun x hx => ?_
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := p) x z' hx
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · change φ' (h.isoPullback.inv w) = z'
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hw2]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw1]

end GlobalTheory.Unif
end
