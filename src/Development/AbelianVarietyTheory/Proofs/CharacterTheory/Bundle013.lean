module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.Algebra.Module.Projective
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem finsum_rootsOfUnity_pow_mul_star {K : Type} [Field K] (θ : K →* ℂ) {N : ℕ} (hN : 0 < N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hω : IsPrimitiveRoot (θ ζ) N) (k l : ℕ) :
    ∑ᶠ α ∈ {α : K | α ^ N = 1}, θ α ^ k * star (θ α ^ l) =
      if k ≡ l [MOD N] then ((N : ℕ) : ℂ) else 0 := by
  classical
  set ω := θ ζ with hωdef
  have hNe : N ≠ 0 := hN.ne'
  have : NeZero N := ⟨hNe⟩

  have hset : {α : K | α ^ N = 1} = (fun i : ℕ => ζ ^ i) '' (↑(Finset.range N) : Set ℕ) := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one h
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hζ.pow_inj hi hj h
  rw [hset, finsum_mem_image hinj, finsum_mem_coe_finset]
  have hnorm : ‖ω‖ = 1 := hω.norm'_eq_one hNe
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hstar : star ω = ω⁻¹ := by
    rw [Complex.inv_eq_conj hnorm]
    rfl

  set u := ω ^ k * (ω ^ l)⁻¹ with hu
  have hterm : ∀ i, θ (ζ ^ i) ^ k * star (θ (ζ ^ i) ^ l) = u ^ i := by
    intro i
    rw [map_pow, star_pow, star_pow, hstar, hu]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hm : ∀ a, ω ^ a = ω ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  have huN : u ^ N = 1 := by
    rw [hu, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul,
      hω.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  split_ifs with hkl
  · have hu1 : u = 1 := by
      rw [hu, hm k, hm l, show k % N = l % N from hkl]
      exact mul_inv_cancel₀ (pow_ne_zero _ hω0)
    simp [hu1]
  · have hu1 : u ≠ 1 := by
      intro h
      have hkl' : ω ^ k = ω ^ l := (mul_inv_eq_one₀ (pow_ne_zero _ hω0)).mp (hu ▸ h)
      apply hkl
      exact hω.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (by rw [← hm, ← hm]; exact hkl')
    rw [geom_sum_eq hu1, huN, sub_self, zero_div]

theorem torus_orthogonality : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  intro F _ _ θ hθ n hn
  classical
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqF : ((Nat.card F : ℕ) : F) = 0 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  set q := Nat.card F with hqdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  set N := q ^ n - 1 with hNdef
  have hN : 0 < N := by omega

  have hNF : (N : F) ≠ 0 := by
    intro h
    have h1 : ((N + 1 : ℕ) : F) = 0 := by
      rw [show N + 1 = q ^ n by omega, Nat.cast_pow, hqF, zero_pow hn.ne']
    rw [Nat.cast_add, h, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1
  have : NeZero (N : F) := ⟨hNF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'

  have hω : IsPrimitiveRoot (θ ζ) N :=
    ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl =>
      hζ.dvd_of_pow_eq_one l (hθ _ _ (pow_ne_zero _ hζ0) one_ne_zero (by rw [map_pow, hl, map_one]))⟩
  exact ⟨⟨ζ, hζ, hω⟩, fun k l => finsum_rootsOfUnity_pow_mul_star θ hN hζ hω k l⟩

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_stabiliser_mul_blocks (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W : Submodule F V) (Φ : Module.End F W → ℂ)
    (Φ' : Module.End F (V ⧸ W) → ℂ) :
    ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        Φ (g.1.restrict g.2) * Φ' (W.mapQ W g.1 (fun x hx => g.2 x hx)) =
      (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
        ((∑ᶠ a, Φ a) * ∑ᶠ b, Φ' b) := by
  classical
  obtain ⟨s, hs⟩ := W.mkQ.exists_rightInverse_of_surjective W.range_mkQ
  have hs' : ∀ y, W.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hmem : ∀ x : V, (LinearMap.id - s ∘ₗ W.mkQ : V →ₗ[F] V) x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self]
  let p : V →ₗ[F] W := LinearMap.codRestrict W _ hmem
  have hp : ∀ x : V, (p x : V) = x - s (W.mkQ x) := fun x => rfl
  have hπ : ∀ x : W, W.mkQ (x : V) = 0 := fun x => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
  have hpι : ∀ x : W, p (x : V) = x := fun x => Subtype.ext (by rw [hp, hπ, map_zero, sub_zero])
  have hps : ∀ y, p (s y) = 0 := fun y => Subtype.ext (by rw [hp, hs', sub_self]; rfl)
  let G : Module.End F W × Module.End F (V ⧸ W) × ((V ⧸ W) →ₗ[F] W) → Module.End F V :=
    fun t => W.subtype ∘ₗ t.1 ∘ₗ p + s ∘ₗ t.2.1 ∘ₗ W.mkQ + W.subtype ∘ₗ t.2.2 ∘ₗ W.mkQ
  have hG : ∀ t x, G t x = (t.1 (p x) : V) + s (t.2.1 (W.mkQ x)) + (t.2.2 (W.mkQ x) : V) :=
    fun t x => rfl
  have hGι : ∀ t (x : W), G t x = (t.1 x : V) := by
    intro t x
    rw [hG, hpι, hπ]; simp
  have hGW : ∀ t, ∀ x ∈ W, G t x ∈ W := by
    intro t x hx
    rw [hGι t ⟨x, hx⟩]; exact (t.1 _).2
  have h1 : ∀ t, (G t).restrict (hGW t) = t.1 := by
    intro t
    ext x
    rw [LinearMap.restrict_coe_apply, hGι]
  have h2 : ∀ t, W.mapQ W (G t) (fun x hx => hGW t x hx) = t.2.1 := by
    intro t
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.mkQ_apply, hG, map_add (f := _), map_add (f := _),
      hπ, hπ, hs', zero_add, add_zero, Submodule.mkQ_apply]
  have h3 : ∀ t, p ∘ₗ G t ∘ₗ s = t.2.2 := by
    intro t
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply]
    rw [hG, hps, hs', map_add (f := _), map_add (f := _), hps, hpι, hpι, map_zero, zero_add, zero_add]
  let e : (Module.End F W × Module.End F (V ⧸ W) × ((V ⧸ W) →ₗ[F] W)) ≃
      {g : Module.End F V // ∀ x ∈ W, g x ∈ W} :=
    { toFun := fun t => ⟨G t, hGW t⟩
      invFun := fun g => (g.1.restrict g.2, W.mapQ W g.1 (fun x hx => g.2 x hx), p ∘ₗ g.1 ∘ₗ s)
      left_inv := fun t => Prod.ext (h1 t) (Prod.ext (h2 t) (h3 t))
      right_inv := by
        intro g
        refine Subtype.ext (LinearMap.ext fun x => ?_)
        show G _ x = _
        rw [hG]
        simp only [LinearMap.restrict_coe_apply, LinearMap.comp_apply]
        have hq : W.mapQ W g.1 (fun x hx => g.2 x hx) (W.mkQ x) = W.mkQ (g.1 (s (W.mkQ x))) := by
          conv_lhs => rw [← hs' (W.mkQ x)]
          rfl
        rw [hq, hp, hp, map_sub]
        abel }
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F W) := Module.finite_of_finite F
  haveI : Finite (Module.End F (V ⧸ W)) := Module.finite_of_finite F
  haveI : Finite ((V ⧸ W) →ₗ[F] W) := Module.finite_of_finite F
  haveI := Fintype.ofFinite (Module.End F W)
  haveI := Fintype.ofFinite (Module.End F (V ⧸ W))
  haveI := Fintype.ofFinite ((V ⧸ W) →ₗ[F] W)
  have hcard : Fintype.card ((V ⧸ W) →ₗ[F] W) =
      Nat.card F ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F),
      Module.finrank_linearMap, mul_comm]
  rw [← finsum_comp_equiv e]
  have : ∀ t, Φ ((e t).1.restrict (e t).2) * Φ' (W.mapQ W (e t).1 (fun x hx => (e t).2 x hx))
      = Φ t.1 * Φ' t.2.1 := by
    intro t
    show Φ ((G t).restrict (hGW t)) * Φ' (W.mapQ W (G t) (fun x hx => hGW t x hx)) = _
    rw [h1, h2]
  rw [finsum_congr this, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow]

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_card_cyclic_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (g : Module.End F V) :
    ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      (Nat.card {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ)
      = (Nat.card F : ℂ) ^ Module.finrank F V := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := Fintype.ofFinite _
  have key : ∀ (W W' : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}) (v : W.1),
      (∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤) →
      (v : V) ∈ W'.1 → W.1 ≤ W'.1 := by
    intro W W' v hv hv' x hx
    have h := hv (W'.1.comap W.1.subtype) (fun y hy => W'.2 _ hy) hv'
    have : (⟨x, hx⟩ : W.1) ∈ W'.1.comap W.1.subtype := h ▸ Submodule.mem_top
    exact this
  let f : (Σ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤}) → V := fun p => (p.2.1 : V)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨W, v, hv⟩ ⟨W', v', hv'⟩ h
      have h' : (v : V) = v' := h
      have hW : W = W' := Subtype.ext (le_antisymm (key W W' v hv (h' ▸ v'.2))
        (key W' W v' hv' (h' ▸ v.2)))
      subst hW
      have : v = v' := Subtype.ext h'
      subst this
      rfl
    · intro v
      let S : Set (Submodule F V) := {U | (∀ x ∈ U, g x ∈ U) ∧ v ∈ U}
      have hinv : ∀ x ∈ sInf S, g x ∈ sInf S := by
        intro x hx
        rw [Submodule.mem_sInf] at hx ⊢
        exact fun p hp => hp.1 x (hx p hp)
      have hv : v ∈ sInf S := by
        rw [Submodule.mem_sInf]
        exact fun p hp => hp.2
      refine ⟨⟨⟨sInf S, hinv⟩, ⟨v, hv⟩, ?_⟩, rfl⟩
      intro U hU hvU
      have hle : sInf S ≤ U.map (sInf S).subtype := by
        refine sInf_le ⟨?_, ⟨_, hvU, rfl⟩⟩
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨_, hU y hy, rfl⟩
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      exact this ▸ hy
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sigma, Module.natCard_eq_pow_finrank (K := F)] at hc
  rw [finsum_eq_sum_of_fintype]
  exact_mod_cast hc

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_int_eq_of_isIntegral_of_mul_eq_int {x : ℂ} (hx : IsIntegral ℤ x) {n k : ℤ}
    (hn : n ≠ 0) (h : (n : ℂ) * x = k) : ∃ j : ℤ, (j : ℂ) = x := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hq : x = algebraMap ℚ ℂ ((k : ℚ) / n) := by
    simp only [eq_ratCast, Rat.cast_div, Rat.cast_intCast]
    rw [eq_div_iff hn', mul_comm, h]
  rw [hq, isIntegral_algebraMap_iff ] at hx
  obtain ⟨j, hj⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  refine ⟨j, ?_⟩
  rw [hq, ← hj]
  simp

theorem exists_int_retraction_of_isIntegral :
    ∀ (ι : Type) [Fintype ι] (r : ι → ℂ), (∀ i, IsIntegral ℤ (r i)) →
      ∃ c : ι → ℤ, ∀ (m : ι → ℤ) (d : ℤ), ∑ i, r i * (m i : ℂ) = d → ∑ i, c i * m i = d := by
  intro ι _ r hr
  classical
  let f : (ι → ℤ) →ₗ[ℤ] ℂ := Fintype.linearCombination ℤ r
  have hf : ∀ m, f m = ∑ i, r i * (m i : ℂ) := by
    intro m
    simp [f, Fintype.linearCombination_apply, mul_comm]
  have hfi : ∀ m, IsIntegral ℤ (f m) := by
    intro m
    rw [hf]
    refine IsIntegral.sum _ fun i _ => (hr i).mul ?_
    exact isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := m i)
  let K : Submodule ℤ (ι → ℤ) := (LinearMap.range (Algebra.linearMap ℤ ℂ)).comap f
  have hK : ∀ m, m ∈ K ↔ ∃ j : ℤ, (j : ℂ) = f m := by
    intro m
    simp [K]
  have : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ K) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n x hx
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    obtain ⟨m, rfl⟩ := K.mkQ_surjective x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK]
    obtain ⟨k, hk⟩ := hx
    refine exists_int_eq_of_isIntegral_of_mul_eq_int (hfi m) hn (k := k) ?_
    rw [hk, map_smul, zsmul_eq_mul]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property K.mkQ (LinearMap.id) K.mkQ_surjective
  let p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id - s ∘ₗ K.mkQ
  have hp : ∀ m, p m ∈ K := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs (K.mkQ m)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this,
      sub_self]
  have hp' : ∀ m ∈ K, p m = m := by
    intro m hm
    have : K.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hm
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, this, map_zero,
      sub_zero]
  choose c hc using fun i : ι => (hK _).mp (hp (Pi.single i 1))
  refine ⟨c, fun m d h => ?_⟩
  have hm : m ∈ K := (hK m).mpr ⟨d, by rw [hf, h]⟩
  have hdec : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
    ext j
    simp [Pi.single_apply]
  have key : ((∑ i, c i * m i : ℤ) : ℂ) = f (p m) := by
    conv_rhs => rw [hdec]

    rw [map_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, ← hc, zsmul_eq_mul, mul_comm]
  rw [hp' m hm, hf, h] at key
  exact_mod_cast key

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem no_norm_eight_of_fourier_vanishing_order_fifteen :
    ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 →
      (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hs hF
  have hinj : Function.Injective (fun j : Fin 15 => ω ^ (j : ℕ)) := by
    intro a b hab
    exact Fin.ext (hω.pow_inj a.2 b.2 hab)
  have hv : (fun i : Fin 15 => ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hinj
    intro j
    have h15 : (ω ^ (j : ℕ)) ^ 15 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hprod : ((ω ^ (j : ℕ)) ^ 3 - 1) *
        ∑ k ∈ Finset.range 15, (c k : ℂ) * (ω ^ (j : ℕ)) ^ k = 0 := by
      by_cases h5 : 5 ∣ (j : ℕ)
      · obtain ⟨m, hm⟩ := h5
        have : (ω ^ (j : ℕ)) ^ 3 = 1 := by
          rw [hm, ← pow_mul, show 5 * m * 3 = 15 * m by ring, pow_mul, hω.pow_eq_one, one_pow]
        rw [this, sub_self, zero_mul]
      · have := hF j j.2 h5
        simp only [pow_mul] at this
        rw [this, mul_zero]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (ω ^ (j : ℕ)) ^ i * ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) 15]
    generalize ω ^ (j : ℕ) = x at h15 hprod
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hprod ⊢
    push_cast
    linear_combination hprod - ((c 12 : ℂ) + c 13 * x + c 14 * x ^ 2) * h15
  have hp : ∀ i : ℕ, i < 15 → c i = c ((i + 12) % 15) := by
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    linarith
  have h3 : c 3 = c 0 := hp 3 (by norm_num)
  have h4 : c 4 = c 1 := hp 4 (by norm_num)
  have h5 : c 5 = c 2 := hp 5 (by norm_num)
  have h6 : c 6 = c 3 := hp 6 (by norm_num)
  have h7 : c 7 = c 4 := hp 7 (by norm_num)
  have h8 : c 8 = c 5 := hp 8 (by norm_num)
  have h9 : c 9 = c 6 := hp 9 (by norm_num)
  have h10 : c 10 = c 7 := hp 10 (by norm_num)
  have h11 : c 11 = c 8 := hp 11 (by norm_num)
  have h12 : c 12 = c 9 := hp 12 (by norm_num)
  have h13 : c 13 = c 10 := hp 13 (by norm_num)
  have h14 : c 14 = c 11 := hp 14 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  rw [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3] at hs
  generalize c 0 ^ 2 = a at hs
  generalize c 1 ^ 2 = b at hs
  generalize c 2 ^ 2 = d at hs
  omega

end GlobalTheory
end
