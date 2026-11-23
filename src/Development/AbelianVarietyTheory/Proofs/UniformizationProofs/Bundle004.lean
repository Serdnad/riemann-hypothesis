module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.Henselian
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
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

section

open Module

namespace GlobalTheory.FiniteCover

theorem finrank_le_of_range_le {K P Q E : Type*} [Field K] [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [Module.Finite K Q]
    (L : P →ₗ[K] E) (hL : Function.Injective L) (B : Q →ₗ[K] E) (h : ∀ p, ∃ q, B q = L p) :
    finrank K P ≤ finrank K Q := by
  rw [← LinearMap.finrank_range_of_inj hL]
  refine (Submodule.finrank_mono (t := LinearMap.range B) ?_).trans B.finrank_range_le
  rintro _ ⟨p, rfl⟩
  exact h p

theorem exists_denominator {A C F F' ι : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field F] [Field F'] [Algebra A C] [Module.Finite A C] [Algebra A F] [IsFractionRing A F]
    [Algebra C F'] [IsFractionRing C F'] [Algebra F F'] [Algebra A F'] [IsScalarTower A F F']
    [IsScalarTower A C F'] [Fintype ι] (e : Basis ι F F') :
    ∃ c : A, c ≠ 0 ∧
      (∀ j (y : C), ∃ a : A, algebraMap A F a = algebraMap A F c * e.repr (algebraMap C F' y) j) ∧
      ∀ j, ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := C)
  obtain ⟨c₁, hc₁⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun p : ι × Fin n => e.repr (algebraMap C F' (g p.2)) p.1)
  have h2 : ∀ j, ∃ c : A, c ≠ 0 ∧ ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
    intro j
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := C) (e j)
    have hinj : Function.Injective (algebraMap A C) := by
      have : Function.Injective (algebraMap A F') := by
        rw [IsScalarTower.algebraMap_eq A F F']
        exact (algebraMap F F').injective.comp (IsFractionRing.injective A F)
      rw [IsScalarTower.algebraMap_eq A C F'] at this
      exact Function.Injective.of_comp this
    have hal : IsAlgebraic A q := (Algebra.IsIntegral.isIntegral (R := A) q).isAlgebraic
    obtain ⟨c, hc, z, hz⟩ := hal.exists_nonzero_dvd hq
    refine ⟨c, hc, z * p, ?_⟩
    have hq' : algebraMap C F' q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    rw [← hpq, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A C F', hz, map_mul, map_mul]
    field_simp
  choose c₂ hc₂ y₂ hy₂ using h2
  refine ⟨c₁ * ∏ j, c₂ j, mul_ne_zero (nonZeroDivisors.coe_ne_zero c₁)
    (Finset.prod_ne_zero_iff.2 fun j _ => hc₂ j), fun j y => ?_, fun j => ?_⟩
  · have hy : y ∈ Submodule.span A (Set.range g) := hg ▸ Submodule.mem_top
    suffices h : ∃ a : A, algebraMap A F a = algebraMap A F c₁ * e.repr (algebraMap C F' y) j by
      obtain ⟨a, ha⟩ := h
      exact ⟨a * ∏ j, c₂ j, by rw [map_mul, map_mul, ha]; ring⟩
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hc₁ (j, k)
      exact ⟨a, by rw [ha, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), map_add (f := _), Finsupp.add_apply, ha, hb, mul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      have : algebraMap C F' (r • x) = algebraMap A F r • algebraMap C F' x := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
      ring
  · refine ⟨(c₁ * ∏ k ∈ Finset.univ.erase j, c₂ k : A) • y₂ j, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), ← mul_assoc, map_mul (algebraMap A F) _ (c₂ j),
      mul_smul (algebraMap A F _), ← hy₂, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_common_multiple {F I : Type*} [Field F] [Fintype I] (A : I → Subring F) (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k) :
    ∃ (a : ℕ) (u : F), u ≠ 0 ∧ ∀ i, ∃ b ∈ A i, u = ρ i ^ a * c i * b := by
  classical
  choose m hm using hext
  let M : I → ℕ := fun i => ∑ k, m i k
  have hM : ∀ i k, c i * (ρ i / ρ k) ^ M i ∈ A k := fun i k => by
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := m i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    change c i * (ρ i / ρ k) ^ (∑ k, m i k) ∈ A k
    rw [hl, pow_add, ← mul_assoc]
    exact mul_mem (hm i k) (pow_mem (hr i k) _)
  refine ⟨∑ i, M i, ∏ i, c i * ρ i ^ M i,
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc i) (pow_ne_zero _ (hρ i)), fun k => ?_⟩
  refine ⟨∏ i ∈ Finset.univ.erase k, c i * (ρ i / ρ k) ^ M i, prod_mem fun i _ => hM i k, ?_⟩
  have e : ∀ i, c i * ρ i ^ M i = ρ k ^ M i * (c i * (ρ i / ρ k) ^ M i) := fun i => by
    have := hρ k
    rw [div_pow]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), div_self (hρ k), one_pow, mul_one, mul_assoc]

theorem finrank_sandwich {K F F' I : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Fintype I] {d : ℕ} (e : Basis (Fin d) F F')
    (A : I → Subring F) (C : I → Subring F') (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k)
    (hAC : ∀ i, ∀ a ∈ A i, algebraMap F F' a ∈ C i)
    (hc₁ : ∀ i j, ∀ y ∈ C i, c i * e.repr y j ∈ A i) (hc₂ : ∀ i j, c i • e j ∈ C i)
    (V W : ℕ → Type*) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)]
    [∀ t, Module K (W t)] (hV : ∀ t, Module.Finite K (V t)) (hW : ∀ t, Module.Finite K (W t))
    (α : ∀ t, V t →ₗ[K] F) (β : ∀ t, W t →ₗ[K] F') (hα : ∀ t, Function.Injective (α t))
    (hβ : ∀ t, Function.Injective (β t))
    (rα : ∀ t x, (∃ v, α t v = x) ↔ ∀ i, ∃ a ∈ A i, x = a * ρ i ^ t)
    (rβ : ∀ t y, (∃ w, β t w = y) ↔ ∀ i, ∃ a ∈ C i, y = a * algebraMap F F' (ρ i ^ t)) :
    ∃ a : ℕ, ∀ t : ℕ, d * finrank K (V t) ≤ finrank K (W (t + a)) ∧
      finrank K (W t) ≤ d * finrank K (V (t + a)) := by
  obtain ⟨a, u, hu, hub⟩ := exists_common_multiple A ρ c hρ hc hr hext
  have hpi : ∀ t, finrank K (Fin d → V t) = d * finrank K (V t) := fun t => by
    rw [Module.finrank_pi_fintype]
    simp
  refine ⟨a, fun t => ⟨?_, ?_⟩⟩
  · rw [← hpi]
    let L : (Fin d → V t) →ₗ[K] F' :=
      ((e.equivFun.symm.toLinearMap.restrictScalars K).comp
        (((LinearMap.mulLeft K u).comp (α t)).compLeft (Fin d)))
    have hL : ∀ v, L v = ∑ j, (u * α t (v j)) • e j := fun v => e.equivFun_symm_apply _
    refine finrank_le_of_range_le L ?_ (β (t + a)) fun v => (rβ _ _).2 fun i => ?_
    · intro v w h
      have h' := e.equivFun.symm.injective h
      funext j
      exact hα t (mul_left_cancel₀ hu (congrFun h' j))
    · obtain ⟨b, hb, rfl⟩ := hub i
      choose x hx hx' using fun j => (rα t _).1 ⟨v j, rfl⟩ i
      refine ⟨∑ j, algebraMap F F' (b * x j) * (c i • e j),
        sum_mem fun j _ => mul_mem (hAC i _ (mul_mem hb (hx j))) (hc₂ i j), ?_⟩
      rw [hL, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx' j]
      simp only [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
  · rw [← hpi]
    let L : W t →ₗ[K] (Fin d → F) := ((LinearMap.mulLeft K u).compLeft (Fin d)).comp
      ((e.equivFun.toLinearMap.restrictScalars K).comp (β t))
    have hL : ∀ w j, L w j = u * e.repr (β t w) j := fun w j => rfl
    refine finrank_le_of_range_le L ?_ ((α (t + a)).compLeft (Fin d)) fun w => ?_
    · intro v w h
      refine hβ t (e.equivFun.injective (funext fun j => ?_))
      exact mul_left_cancel₀ hu (congrFun h j)
    · have key : ∀ j, ∃ v, α (t + a) v = L w j := fun j => (rα _ _).2 fun i => by
        obtain ⟨b, hb, hub⟩ := hub i
        obtain ⟨y, hy, hy'⟩ := (rβ t _).1 ⟨w, rfl⟩ i
        refine ⟨b * (c i * e.repr y j), mul_mem hb (hc₁ i j y hy), ?_⟩
        rw [hL, hy', mul_comm y, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hub,
          pow_add]
        ring
      choose v hv using key
      exact ⟨v, funext hv⟩

end GlobalTheory.FiniteCover
end

section

namespace GlobalTheory

theorem coeff_eq_zero_of_sum_smul_eq_zero_of_separating {Y A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (P : (Y → A) → Prop) (h1 : P 1)
    (hmul : ∀ t t', P t → P t' → P (t * t')) (s : Finset Y)
    (hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → ∃ t, P t ∧ IsUnit (t y - t z))
    (a : Y → M) (h : ∀ t, P t → ∑ y ∈ s, t y • a y = 0) : ∀ y ∈ s, a y = 0 := by
  classical
  induction s using Finset.strongInduction generalizing a with
  | H s ih =>
    intro y₀ hy₀
    by_cases hz : ∃ z ∈ s, z ≠ y₀
    · obtain ⟨z, hzs, hzy⟩ := hz
      obtain ⟨u, hu, hunit⟩ := hsep y₀ hy₀ z hzs (Ne.symm hzy)

      set b : Y → M := fun y => (u y - u z) • a y with hb
      have hbrel : ∀ t, P t → ∑ y ∈ s.erase z, t y • b y = 0 := by
        intro t ht
        rw [Finset.sum_erase s (by simp [hb])]
        have e : ∀ y, t y • b y = (t * u) y • a y - u z • (t y • a y) := by
          intro y
          simp only [hb, Pi.mul_apply, smul_smul, ← sub_smul]
          congr 1
          ring
        simp only [e, Finset.sum_sub_distrib, ← Finset.smul_sum, h t ht, h (t * u) (hmul t u ht hu),
          smul_zero, sub_zero]
      have hsub : s.erase z ⊂ s := Finset.erase_ssubset hzs
      have key := ih (s.erase z) hsub
        (fun y hy w hw hne => hsep y (Finset.mem_of_mem_erase hy) w (Finset.mem_of_mem_erase hw) hne)
        b hbrel y₀ (Finset.mem_erase.mpr ⟨Ne.symm hzy, hy₀⟩)
      exact (hunit.smul_eq_zero).mp key
    · push Not at hz
      have := h 1 h1
      rw [Finset.sum_eq_single_of_mem y₀ hy₀ (fun z hz' hne => absurd (hz z hz') hne)] at this
      simpa using this

theorem laurent_coeff_eq_zero_of_vanish_torsion :
    ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (n : ℕ), n.Prime →
    ∀ s : Finset Y, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (A : Type) [CommRing A] [IsLocalRing A] (ζ : A),
    IsUnit (n : A) → ζ ^ (n ^ j) = 1 → IsPrimitiveRoot (IsLocalRing.residue A ζ) (n ^ j) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] (a : Y → M),
    (∀ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) →
      ∑ y ∈ s, (t (Multiplicative.ofAdd y) : A) • a y = 0) → ∀ y ∈ s, a y = 0 := by
  intro Y _ _ _ n hn s
  let b := Module.Free.chooseBasis ℤ Y

  refine ⟨∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs, ?_⟩
  intro j hj A _ _ ζ _ hζ hprim M _ _ a ha
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  let u : Aˣ := Units.ofPowEqOne ζ (n ^ j) hζ hN
  have hu : u ^ (n ^ j) = 1 := Units.pow_ofPowEqOne hζ hN

  let χ : _ → Multiplicative Y →* Aˣ := fun i =>
    (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hχ : ∀ i y, χ i (Multiplicative.ofAdd y) = u ^ (b.repr y i) := by
    intro i y
    simp [χ, zpowersHom]
  have hχord : ∀ i y, χ i y ^ (n ^ j) = 1 := by
    intro i y
    rw [show y = Multiplicative.ofAdd (Multiplicative.toAdd y) from rfl, hχ, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  let P : (Y → A) → Prop := fun f =>
    ∃ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) ∧ f = fun y => (t (Multiplicative.ofAdd y) : A)
  refine coeff_eq_zero_of_sum_smul_eq_zero_of_separating P ⟨1, fun _ => one_pow _, by funext; simp⟩
    ?_ s ?_ a ?_
  · rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t * t', fun y => by rw [MonoidHom.mul_apply, mul_pow, ht, ht', one_mul],
      by funext y; simp⟩
  · intro y hy z hz hyz
    have hw : b.repr (y - z) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact sub_ne_zero.mpr hyz
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hw
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    refine ⟨_, ⟨χ i, hχord i, rfl⟩, ?_⟩
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hχ, hχ, map_sub]
    let v : (IsLocalRing.ResidueField A)ˣ := Units.map (IsLocalRing.residue A).toMonoidHom u
    have hv : IsPrimitiveRoot v (n ^ j) := IsPrimitiveRoot.coe_units_iff.mp (by simpa [v, u] using hprim)
    have hres : ∀ k : ℤ, IsLocalRing.residue A ((u ^ k : Aˣ) : A) = ((v ^ k : _ˣ) : _) := by
      intro k
      rw [show v ^ k = Units.map (IsLocalRing.residue A).toMonoidHom (u ^ k) from (map_zpow _ u k).symm]
      rfl
    rw [hres, hres, sub_ne_zero, Ne, Units.val_inj, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, ← Finsupp.sub_apply,
      ← map_sub, hv.zpow_eq_one_iff_dvd]
    intro hdvd
    apply hi
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    have h1 : (b.repr (y - z) i).natAbs ≤ ∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun p : Y × Y => ∑ i, (b.repr (p.1 - p.2) i).natAbs)
        (fun _ _ => Nat.zero_le _) (show (y, z) ∈ s ×ˢ s from Finset.mem_product.mpr ⟨hy, hz⟩))
      exact Finset.single_le_sum (f := fun i => (b.repr (y - z) i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : j < n ^ j := Nat.lt_pow_self hn.one_lt
    simp only [Int.natAbs_natCast]
    omega
  · rintro _ ⟨t, ht, rfl⟩
    exact ha t ht

end GlobalTheory
end

section

namespace GlobalTheory

open TensorProduct

noncomputable def rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) : TensorProduct F E E' →ₗ[F] E :=
  (TensorProduct.rid F E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l

theorem rightContract_tmul {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (x : E) (y : E') :
    rightContract l (x ⊗ₜ[F] y) = l y • x := by
  simp [rightContract]

theorem rightContract_map {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (f : E →ₗ[F] E) (g : E' →ₗ[F] E')
    (w : TensorProduct F E E') :
    rightContract l (TensorProduct.map f g w) = f (rightContract (l ∘ₗ g) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [rightContract_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem eq_zero_of_rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (w : TensorProduct F E E')
    (h : ∀ l : E' →ₗ[F] F, rightContract l w = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F E'
  have key : ∀ (i) (v : TensorProduct F E E'),
      TensorProduct.equivFinsuppOfBasisRight b v i = rightContract (b.coord i) v := by
    intro i v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [rightContract_tmul]
    | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, h]
  simp

theorem eigenTensor_full_left_support :
    ∀ (F : Type) [Field F] (E E' Ix : Type) [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (Φ : Ix → (E →ₗ[F] E)) (Φ' : Ix → (E' ≃ₗ[F] E')), (∀ U : Submodule F E, (∀ i, ∀ v ∈ U, Φ i v ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ w : TensorProduct F E E', w ≠ 0 → (∀ i, ∃ r : F, TensorProduct.map (Φ i) (Φ' i : E' →ₗ[F] E') w = r • w) → ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E' →ₗ[F] E') w = 0 → π = 0 := by
  intro F _ E E' Ix _ _ _ _ Φ Φ' hirr w hw heig π hπ
  let U : Submodule F E := Submodule.span F (Set.range fun l : E' →ₗ[F] F => rightContract l w)
  have hmem : ∀ l : E' →ₗ[F] F, rightContract l w ∈ U := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hstab : ∀ i, ∀ v ∈ U, Φ i v ∈ U := by
    intro i v hv
    have hle : U ≤ U.comap (Φ i) := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      obtain ⟨r, hr⟩ := heig i
      have h1 := rightContract_map (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) (Φ i) (Φ' i : E' →ₗ[F] E') w
      have h2 : (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) ∘ₗ (Φ' i : E' →ₗ[F] E') = l := by
        ext y; simp
      rw [h2, hr, map_smul] at h1
      show Φ i (rightContract l w) ∈ U
      rw [← h1]
      exact U.smul_mem _ (hmem _)
    exact hle hv
  rcases hirr U hstab with hU | hU
  · exfalso
    apply hw
    apply eq_zero_of_rightContract
    intro l
    have := hmem l
    rwa [hU, Submodule.mem_bot] at this
  · have hle : U ≤ LinearMap.ker π := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      have h1 := rightContract_map l π LinearMap.id w
      rw [hπ, map_zero, LinearMap.comp_id] at h1
      exact h1.symm
    rw [hU, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle

end GlobalTheory
end

section

namespace GlobalTheory.PrecompleteOfPowLe

universe u

theorem isPrecomplete_of_le_of_pow_le {A : Type u} [CommRing A] {I J : Ideal A} (hJI : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [hJ : IsPrecomplete J A] : IsPrecomplete I A := by
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m =>
    calc I ^ ((e + 1) * m) ≤ I ^ (e * m) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right m (Nat.le_succ e))
      _ = (I ^ e) ^ m := pow_mul I e m
      _ ≤ J ^ m := Ideal.pow_right_mono he m
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := hJ.prec (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left (e + 1) hmn)).mono (Submodule.smul_mono_left (h1 m)))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ (e + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos e)
  exact (hf hn).trans ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)))

end GlobalTheory.PrecompleteOfPowLe
end

section

namespace GlobalTheory

theorem exists_mem_pow_of_ratio_of_torsionFree :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O]
      (io : V →+* O), (∀ v : V, v ≠ 0 → ∀ x : O, io v * x = 0 → x = 0) →
      ∀ (f h : O) (p q : V) (m n : ℕ), q ≠ 0 → io q * f = io p * h →
      f ∈ (IsLocalRing.maximalIdeal V ^ (m + n)).map io →
      h ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map io →
      ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
  intro V _ _ _ O _ io htf f h p q m n hq e hf hh
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : IsLocalRing.maximalIdeal V = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπn : π ^ n ∈ IsLocalRing.maximalIdeal V ^ n := by
    rw [hm, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
  have key : π ^ n * q ∣ p → ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
    rintro ⟨c, hc⟩
    exact ⟨π ^ n * c, Ideal.mul_mem_right _ _ hπn, by rw [hc]; ring⟩
  rcases ValuationRing.dvd_total (π ^ n * q) p with hd | ⟨c, hc⟩
  · exact key hd
  by_cases hu : IsUnit c
  · apply key
    obtain ⟨u, rfl⟩ := hu
    exact ⟨(u⁻¹ : Vˣ), by rw [hc, mul_assoc, Units.mul_inv, mul_one]⟩
  exfalso
  apply hh
  have hcm : c ∈ IsLocalRing.maximalIdeal V := hu
  rw [hm, Ideal.mem_span_singleton] at hcm
  obtain ⟨d, rfl⟩ := hcm
  have hp : p ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero n hπ.ne_zero) hq (by simpa using hc)
  rw [hm, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨g, rfl⟩ := hf
  refine ⟨io d * g, ?_⟩
  have h0 := htf p hp (h - io (π ^ (m + 1)) * (io d * g)) (by
    have hc' := congrArg io hc
    simp only [map_mul, map_pow] at hc' e ⊢
    linear_combination (io π ^ m * g) * hc' - e)
  exact sub_eq_zero.mp h0

end GlobalTheory
end
