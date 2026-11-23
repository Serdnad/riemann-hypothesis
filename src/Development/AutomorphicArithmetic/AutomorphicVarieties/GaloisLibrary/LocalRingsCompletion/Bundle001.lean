module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Order
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem binom_prime {R : Type*} [CommRing R] {l : ℕ} (hl : l.Prime) (y : R) :
    ∃ s : R, (1 + y) ^ l - 1 = y ^ l + l * y * (1 + y * s) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (1 : Polynomial ℤ) Polynomial.X
  have h1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) hr
  have hl1 : (1 : ℕ) ≠ l := hl.one_lt.ne
  have e : ((l : Polynomial ℤ) * 1 * Polynomial.X * r) = Polynomial.C (l : ℤ) * (Polynomial.X * r) := by
    simp [mul_assoc]
  simp only [Polynomial.coeff_one_add_X_pow, Nat.choose_one_right, one_pow, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, if_neg hl1, e, Polynomial.coeff_C_mul, Polynomial.coeff_one] at h1
  have h2 : (Polynomial.X * r).coeff 1 = r.coeff 0 := Polynomial.coeff_X_mul r 0
  rw [h2] at h1
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have h3 : r.coeff 0 = 1 := by
    apply mul_left_cancel₀ hl0
    simpa using h1.symm
  have h4 : r = 1 + Polynomial.X * r.divX := by
    have := Polynomial.X_mul_divX_add r
    rw [h3] at this
    rw [add_comm]
    simpa using this.symm
  refine ⟨Polynomial.aeval y r.divX, ?_⟩
  have h5 := congrArg (Polynomial.aeval y) hr
  rw [h4] at h5
  simp only [map_pow, map_add (f := _), map_one, Polynomial.aeval_X, map_mul, map_natCast] at h5
  rw [h5]
  ring

private theorem binom_one {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ s : R, (1 + y) ^ n - 1 = y * (n + y * s) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨n + s + y * s, ?_⟩
    rw [pow_succ, sub_eq_iff_eq_add.1 hs]
    push_cast
    ring

private theorem isUnit_add_mem {O : Type*} [CommRing O] [IsLocalRing O] {a b : O} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal O) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal O := h
  have h2 : a ∈ maximalIdeal O := by simpa using (maximalIdeal O).sub_mem h1 hb
  exact h2 ha

private theorem step_prime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {l : ℕ} (hl : l.Prime) {y : O} (hy : y ∈ maximalIdeal O)
    (h : addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O y) :
    addVal O ((1 + y) ^ l - 1) = addVal O y + addVal O (l : O) := by
  have h' : addVal O (l : O) < addVal O (y ^ (l - 1)) := by
    rwa [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul]
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h'.le
  have hcm : c ∈ maximalIdeal O := by
    intro hu
    rw [hc, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu,
      add_zero] at h'
    exact lt_irrefl _ h'
  obtain ⟨s, hs⟩ := binom_prime hl y
  have e : y ^ l = y * (l * c) := by
    rw [← hc, ← pow_succ', Nat.sub_add_cancel hl.one_lt.le]
  have hu : IsUnit (1 + (y * s + c)) :=
    isUnit_add_mem isUnit_one ((maximalIdeal O).add_mem (Ideal.mul_mem_right _ _ hy) hcm)
  have e2 : (1 + y) ^ l - 1 = y * l * (1 + (y * s + c)) := by rw [hs, e]; ring
  rw [e2, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu, add_zero]

private theorem lte_nat {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {l : ℕ} (hl : l.Prime) (hlm : (l : O) ∈ maximalIdeal O) (n : ℕ) :
    ∀ y : O, y ∈ maximalIdeal O → addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O y →
      addVal O ((1 + y) ^ n - 1) = addVal O y + addVal O (n : O) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    by_cases hd : l ∣ n
    · obtain ⟨k, rfl⟩ := hd
      have hk : 0 < k := Nat.pos_of_mul_pos_left hn
      have hlt : k < l * k := lt_mul_of_one_lt_left hk hl.one_lt
      have h1 := step_prime hl hy h
      have hy' : (1 + y) ^ l - 1 ∈ maximalIdeal O := by
        obtain ⟨s, hs⟩ := binom_one y l
        rw [hs]
        exact Ideal.mul_mem_right _ _ hy
      have h2 := ih k hlt _ hy' (h.trans_le (by
        rw [h1]
        gcongr
        exact le_self_add))
      rw [add_sub_cancel, ← pow_mul, h1] at h2
      rw [h2, Nat.cast_mul, IsDiscreteValuationRing.addVal_mul, add_assoc]
    · have hu : IsUnit (n : O) := by
        by_contra hnu
        have hnm : (n : O) ∈ maximalIdeal O := hnu
        have hc : IsCoprime (l : O) (n : O) := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).cast
        obtain ⟨a, b, hab⟩ := hc
        have : (1 : O) ∈ maximalIdeal O :=
          hab ▸ (maximalIdeal O).add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hnm)
        exact this isUnit_one
      obtain ⟨s, hs⟩ := binom_one y n
      rw [hs, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu,
        IsDiscreteValuationRing.addVal_eq_zero_iff.2 (isUnit_add_mem hu (Ideal.mul_mem_right _ _ hy))]

theorem UpperTheory.V.abelian₂.lte :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ), l.Prime → (l : O) ∈ maximalIdeal O → ∀ u : oneUnits O,
      addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O (pt u : O) → (∀ n : ℤ, addVal O (pt (u ^ n) : O) = addVal O (pt u : O) + addVal O (n : O)) := by
  intro O _ _ _ _ l hl hlm u h n
  have key : ∀ k : ℕ, addVal O (((u : Oˣ) : O) ^ k - 1) = addVal O (pt u : O) + addVal O (k : O) := by
    intro k
    have := lte_nat hl hlm k _ (pt u).2 h
    rwa [coe_pt, add_sub_cancel] at this
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Int.cast_natCast, ← key k, coe_pt]
    simp
  · have e : (pt (u ^ (-(k : ℤ))) : O) = ((-((u : Oˣ) ^ k)⁻¹ : Oˣ) : O) * (((u : Oˣ) : O) ^ k - 1) := by
      rw [coe_pt, zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, Units.val_neg, neg_mul, mul_sub,
        Units.inv_mul, mul_one, neg_sub]
      simp
    rw [e, IsDiscreteValuationRing.addVal_mul, key k,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (Units.isUnit _), zero_add, Int.cast_neg,
      Int.cast_natCast, AddValuation.map_neg]
end

section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem len_mid {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (h : N →ₗ[R] P)
    (e : Function.Exact f h) :
    Module.length R N = Module.length R (LinearMap.range f) + Module.length R (LinearMap.range h) := by
  refine Module.length_eq_add_of_exact (LinearMap.range f).subtype h.rangeRestrict
    (Submodule.injective_subtype _) h.surjective_rangeRestrict ?_
  intro n
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero]
  change h n = 0 ↔ _
  rw [e n]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨⟨f m, m, rfl⟩, rfl⟩
  · rintro ⟨⟨_, m, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩

private def tmap {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : R) (f : M →ₗ[R] N) :
    Submodule.torsionBy R M g →ₗ[R] Submodule.torsionBy R N g :=
  f.restrict fun x hx => by
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [← map_smul, hx, map_zero]

private theorem ex_tors {R : Type} (M : Type) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (Submodule.torsionBy R M g).subtype (g • (LinearMap.id : M →ₗ[R] M)) := by
  intro x
  constructor
  · intro hx
    refine ⟨⟨x, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, rfl⟩
    simpa using hx
  · rintro ⟨⟨y, hy⟩, rfl⟩
    simpa using (Submodule.mem_torsionBy_iff _ _).1 hy

private theorem ex_quot {R : Type} (M : Type) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (g • (LinearMap.id : M →ₗ[R] M)) (g • (⊤ : Submodule R M)).mkQ := by
  intro x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact ⟨b, by simp⟩
  · rintro ⟨b, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, Submodule.mem_top, by simp⟩

theorem UpperTheory.V.abelian₂.snake_len :
    ∀ (R : Type) [CommRing R] (g : R) (A B D : Type) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D] [Module R D]
      (i : A →ₗ[R] B) (j : B →ₗ[R] D), Function.Injective i → Function.Surjective j → Function.Exact i j →
      invLen g A + invLen g D + coinvLen g B = invLen g B + coinvLen g A + coinvLen g D ∧
        invLen g B ≤ invLen g A + invLen g D ∧ coinvLen g B ≤ coinvLen g A + coinvLen g D ∧
        invLen g A ≤ invLen g B ∧ coinvLen g D ≤ coinvLen g B ∧
        coinvLen g A ≤ invLen g D + coinvLen g B ∧ invLen g D ≤ invLen g B + coinvLen g A := by
  intro R _ g A B D _ _ _ _ _ _ i j hi hj hij
  have h₁ : i ∘ₗ (g • LinearMap.id : A →ₗ[R] A) = (g • LinearMap.id : B →ₗ[R] B) ∘ₗ i := by
    ext a
    simp
  have h₂ : j ∘ₗ (g • LinearMap.id : B →ₗ[R] B) = (g • LinearMap.id : D →ₗ[R] D) ∘ₗ j := by
    ext b
    simp
  let G : QuotSMulTop g A →ₗ[R] QuotSMulTop g B := Submodule.mapQ _ _ i (by
    intro a ha
    rw [Submodule.mem_comap]
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  let H : QuotSMulTop g B →ₗ[R] QuotSMulTop g D := Submodule.mapQ _ _ j (by
    intro a ha
    rw [Submodule.mem_comap]
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have hG : G ∘ₗ (g • ⊤ : Submodule R A).mkQ = (g • ⊤ : Submodule R B).mkQ ∘ₗ i := by
    ext a
    rfl
  have hδr := SnakeLemma.exact_δ'_right (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂ (Submodule.torsionBy R B g).subtype (ex_tors B g)
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    hj hi (tmap g j) (by ext x; rfl) (Submodule.injective_subtype _)
  have hδl := SnakeLemma.exact_δ'_left (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    (g • ⊤ : Submodule R B).mkQ (ex_quot B g) hj hi G hG (Submodule.mkQ_surjective _)
  have e1 : Function.Exact (tmap g i) (tmap g j) := by
    intro x
    constructor
    · intro hx
      have hx' : j x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨a, ha⟩ := (hij x.1).1 hx'
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      rw [Submodule.mem_torsionBy_iff]
      apply hi
      rw [map_smul, ha, map_zero]
      exact (Submodule.mem_torsionBy_iff _ _).1 x.2
    · rintro ⟨a, rfl⟩
      exact Subtype.ext (hij.apply_apply_eq_zero a.1)
  have i1 : Function.Injective (tmap g i) := fun x y hxy =>
    Subtype.ext (hi (congrArg Subtype.val hxy))
  have e4 : Function.Exact G H := by
    intro y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    constructor
    · intro hy
      change Submodule.Quotient.mk (j b) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨d, -, hd⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      obtain ⟨b', rfl⟩ := hj d
      obtain ⟨a, ha⟩ := (hij (b - g • b')).1 (by rw [map_sub, map_smul, hd, sub_self])
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (i a) = Submodule.Quotient.mk b
      rw [ha, Submodule.Quotient.eq, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    · rintro ⟨x, hx⟩
      rw [← hx]
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
      change Submodule.Quotient.mk (j (i a)) = 0
      rw [hij.apply_apply_eq_zero, Submodule.Quotient.mk_zero]
  have s4 : Function.Surjective H := by
    intro y
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨b, rfl⟩ := hj d
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  have L1 := len_mid (tmap g i) (tmap g j) e1
  have L2 := len_mid _ _ hδr
  have L3 := len_mid _ _ hδl
  have L4 := len_mid G H e4
  have r1 : Module.length R (LinearMap.range (tmap g i)) =
      Module.length R (Submodule.torsionBy R A g) :=
    (LinearEquiv.ofInjective _ i1).length_eq.symm
  have r4 : Module.length R (LinearMap.range H) = Module.length R (QuotSMulTop g D) := by
    rw [LinearMap.range_eq_top.2 s4, Module.length_top]
  have arith : ∀ p x y z q : ℕ∞,
      p + (x + y) + (z + q) = p + x + (y + z) + q ∧ p + x ≤ p + (x + y) ∧
        z + q ≤ y + z + q ∧ p ≤ p + x ∧ q ≤ z + q ∧ y + z ≤ x + y + (z + q) ∧
        x + y ≤ p + x + (y + z) := by
    intro p x y z q
    exact ⟨by ring, le_iff_exists_add.2 ⟨y, by ring⟩, le_iff_exists_add.2 ⟨y, by ring⟩,
      le_iff_exists_add.2 ⟨x, by ring⟩, le_iff_exists_add.2 ⟨z, by ring⟩,
      le_iff_exists_add.2 ⟨x + q, by ring⟩, le_iff_exists_add.2 ⟨p + z, by ring⟩⟩
  unfold invLen coinvLen
  rw [L1, L2, L3, L4, r1, r4]
  exact arith _ _ _ _ _
end

section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.mu_dvd :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧,
      (∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f) ∧ (mu f = 0 ↔ map (residue O) f ≠ 0) ∧
        (mu f = 0 → lam f = (map (residue O) f).order.toNat) ∧
        ∀ m : ℕ, mu (C ϖ ^ m * f) = m + mu f ∧ lam (C ϖ ^ m * f) = lam f := by
  intro O _ _ _ ϖ hϖ f
  have hpow : ∀ m : ℕ, addVal O (ϖ ^ m) = m := by
    intro m
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  have hdvd : ∀ m : ℕ, C ϖ ^ m ∣ f ↔ ∀ n, ϖ ^ m ∣ coeff n f := by
    intro m
    constructor
    · rintro ⟨g, rfl⟩ n
      rw [← map_pow, PowerSeries.coeff_C_mul]
      exact dvd_mul_right _ _
    · intro h
      choose g hg using h
      refine ⟨PowerSeries.mk g, ?_⟩
      ext n
      rw [← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hg n]
  have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f := by
    intro m
    rw [hdvd, mu, le_iInf_iff]
    refine forall_congr' fun n => ?_
    rw [← hpow m, IsDiscreteValuationRing.addVal_le_iff_dvd]
  have hmu0 : mu f = 0 → map (residue O) f ≠ 0 := by
    intro h hzero
    have hc := addVal_coeff_lam f
    rw [h, IsDiscreteValuationRing.addVal_eq_zero_iff, ← residue_ne_zero_iff_isUnit] at hc
    apply hc
    rw [← PowerSeries.coeff_map, hzero, map_zero]
  refine ⟨h1, ⟨hmu0, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, coeff n (map (residue O) f) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h (PowerSeries.ext fun n => by simpa using hall n)
    rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
      ← IsDiscreteValuationRing.addVal_eq_zero_iff] at hn
    have hle := mu_le f n
    rw [hn] at hle
    exact le_antisymm hle bot_le
  · intro h
    have hord : (map (residue O) f).order = (lam f : ℕ∞) := by
      rw [PowerSeries.order_eq_nat]
      constructor
      · rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
          ← IsDiscreteValuationRing.addVal_eq_zero_iff, addVal_coeff_lam, h]
      · intro i hi
        rw [PowerSeries.coeff_map]
        by_contra hne
        have hu : IsUnit (coeff i f) := (residue_ne_zero_iff_isUnit _).1 hne
        rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
        have hli : lam f ≤ i := Nat.sInf_le (by
          show addVal O (coeff i f) = mu f
          rw [hu, h])
        omega
    rw [hord, ENat.toNat_coe]
  · intro m
    have hcoeff : ∀ n, addVal O (coeff n (C ϖ ^ m * f)) = m + addVal O (coeff n f) := by
      intro n
      rw [← map_pow, PowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, hpow]
    have hmu : mu (C ϖ ^ m * f) = m + mu f := by
      rw [mu, mu, ENat.add_iInf]
      exact iInf_congr hcoeff
    refine ⟨hmu, ?_⟩
    rw [lam, lam]
    congr 1
    ext n
    simp only [Set.mem_setOf_eq, hcoeff, hmu]
    exact ⟨fun h => WithTop.add_left_cancel (ENat.coe_ne_top m) h, fun h => by rw [h]⟩
end
