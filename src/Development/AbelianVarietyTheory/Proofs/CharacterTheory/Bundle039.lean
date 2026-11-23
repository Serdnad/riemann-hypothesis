module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle027
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle038
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle021
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_mem_lin_comb_of_finite {α : Type} [Finite α] (S : Set α) (a b : ℂ) (u v : α → ℂ) :
    ∑ᶠ x ∈ S, (a * u x - b * v x) = a * (∑ᶠ x ∈ S, u x) - b * ∑ᶠ x ∈ S, v x := by
  have hS : S.Finite := Set.toFinite S
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

theorem eq_zero_of_mass_charpoly_eq_zero (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ) (hc : IsClassFn φ) (hp : IsPrimitive φ)
    (g : Module.End F V) (hm : mass φ (LinearMap.charpoly g) = 0) : φ g = 0 := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective (fun h : Module.End F V => (h : V → V))
    DFunLike.coe_injective
  rcases Nat.eq_zero_or_pos (Module.finrank F V) with h0 | hpos
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    have hset : {g' : Module.End F V | LinearMap.charpoly g' = LinearMap.charpoly g} = {g} := by
      ext g'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have : g' = g := Subsingleton.elim _ _
      simp [this]
    rw [mass, hset, finsum_mem_singleton] at hm
    exact hm
  by_cases hprim : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m
  swap
  · exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hc hp hpos g hprim
  obtain ⟨f, m, hfm, hf, hm0, hg⟩ := hprim
  set s : F[X] → ℂ := fun P => (P.natDegree : ℂ) with hs
  have hsa : IsAdditive s := isAdditive_natDegree
  have hπc : IsClassFn (psi s V) := fun e x => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s V V e x
  have hπp : IsPrimitive (psi s V) := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V s hsa
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hmass : mass (psi s V) (LinearMap.charpoly g) ≠ 0 := by
    rw [GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V s hsa _ (LinearMap.charpoly_monic g) hdeg, hdeg, hg,
      (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F s hsa).2.1 f m hfm hf hm0]
    have h1 : glCard F (Module.finrank F V) ≠ 0 := by
      rw [glCard]
      exact_mod_cast (Nat.card_pos (α := GL (Fin (Module.finrank F V)) F)).ne'
    have h2 : s f ≠ 0 := by
      simp only [hs]
      exact_mod_cast hf.natDegree_pos.ne'
    have h3 : (Nat.card F : ℂ) ^ Module.finrank F V - 1 ≠ 0 := by
      have hq : 1 < Nat.card F := Finite.one_lt_card
      have : 1 < Nat.card F ^ Module.finrank F V := Nat.one_lt_pow hpos.ne' hq
      rw [sub_ne_zero]
      exact_mod_cast this.ne'
    exact div_ne_zero (mul_ne_zero h1 h2) h3
  have hex : ∃ g₀ : Module.End F V, LinearMap.charpoly g₀ = f ^ m ∧ aeval g₀ f = 0 ∧ psi s V g₀ ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hmass
    rw [mass]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary F V _ hπc hπp f m hf hne x (hg ▸ hx)
  obtain ⟨g₀, hg₀, hfg₀, hπ₀⟩ := hex
  have hconj : ∀ g₁ : Module.End F V, aeval g₁ f = 0 → ∃ e : V ≃ₗ[F] V, e.conj g₀ = g₁ := by
    intro g₁ h₁
    refine GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g₀ g₁ f 1 hf (by simpa using hfg₀) (by simpa using h₁) fun j => ?_
    rw [map_pow, map_pow, hfg₀, h₁]
  set φ' : Module.End F V → ℂ := fun x => psi s V g₀ * φ x - φ g₀ * psi s V x with hφ'
  have hc' : IsClassFn φ' := fun e x => by simp only [hφ', hc e x, hπc e x]
  have hp' : IsPrimitive φ' := fun A h1 h2 x hx => by
    simp only [hφ']
    rw [finsum_mem_lin_comb_of_finite _ _ _ (fun h => φ (x + h)) (fun h => psi s V (x + h)),
      hp A h1 h2 x hx, hπp A h1 h2 x hx]
    simp
  have hz : ∀ x : Module.End F V, LinearMap.charpoly x = f ^ m → φ' x = 0 := by
    refine GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary F V φ' hc' hp' f m hf fun x _ hx => ?_
    obtain ⟨e, rfl⟩ := hconj x hx
    simp only [hφ', hc e g₀, hπc e g₀]
    ring
  have hm' : mass φ' (LinearMap.charpoly g) = 0 := by
    rw [mass]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun x hx => hz x (hg ▸ hx)
  have hlin : mass φ' (LinearMap.charpoly g) = psi s V g₀ * mass φ (LinearMap.charpoly g) -
      φ g₀ * mass (psi s V) (LinearMap.charpoly g) :=
    finsum_mem_lin_comb_of_finite _ _ _ _ _
  rw [hm', hm, mul_zero, zero_sub, eq_comm, neg_eq_zero] at hlin
  have h0 : φ g₀ = 0 := (mul_eq_zero.mp hlin).resolve_right hmass
  have := hz g hg
  simp only [hφ', h0, zero_mul, sub_zero] at this
  exact (mul_eq_zero.mp this).resolve_left hπ₀

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem IsAdditive.map_pow_monic {F : Type} [Field F] {s : F[X] → ℂ} (hs : IsAdditive s) {f : F[X]}
    (hf : f.Monic) (m : ℕ) : s (f ^ m) = m * s f := by
  induction m with
  | zero =>
    have h := hs 1 1 monic_one monic_one
    rw [mul_one] at h
    rw [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h
  | succ m ih =>
    rw [pow_succ, hs _ _ (hf.pow m) hf, ih]
    push_cast
    ring

theorem ipGL_psi_rootSum (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (hn : 0 < Module.finrank F V)
    (k l : ℕ) :
    ipGL (psi (rootSum θ k) V) (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) =
      glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter
        (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)])).card : ℂ) := by
  classical
  set n := Module.finrank F V with hn_def
  set q := Nat.card F with hq_def
  have hq : 1 < q := Finite.one_lt_card
  have hN : 0 < q ^ n - 1 := by
    have : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
    omega
  obtain ⟨hadd, -⟩ := GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k
  have hclass : IsClassFn (psi (rootSum θ k) V) := fun e g => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F _ V V e g
  have hprim := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hadd
  rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ _ hclass hprim hn l]

  have hS : {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} =
      ↑((nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset) := by
    ext α
    simp [Polynomial.mem_nthRoots hN]
  rw [hS, finsum_mem_coe_finset]

  have key : ∀ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      ((n / (minpoly F α).natDegree : ℕ) : ℂ) *
          mass (psi (rootSum θ k) V) (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) =
        glCard F n / ((q : ℂ) ^ n - 1) * ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) * star (θ α ^ l) := by
    intro α hα
    have hα' : α ∈ {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} := by
      rw [hS]; exact hα
    obtain ⟨hdvd, -, hroot⟩ := GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum F θ n hn α hα'
    have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have hmon : (minpoly F α).Monic := minpoly.monic hint
    have hirr : Irreducible (minpoly F α) := minpoly.irreducible hint
    have hd : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
    have hm : 0 < n / (minpoly F α).natDegree := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
    have hdeg : (minpoly F α ^ (n / (minpoly F α).natDegree)).natDegree = n := by
      rw [hmon.natDegree_pow]
      exact Nat.div_mul_cancel hdvd
    rw [GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hadd _ (hmon.pow _) hdeg, hdeg,
      (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F _ hadd).2.1 _ _ hmon hirr hm]
    have h1 : ((n / (minpoly F α).natDegree : ℕ) : ℂ) * rootSum θ k (minpoly F α) =
        ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) := by
      rw [← IsAdditive.map_pow_monic hadd hmon, hroot]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, ← pow_mul, Nat.mul_comm]
    rw [← Finset.sum_mul, ← h1]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]

  have h2 : ∀ i, ∑ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      θ α ^ (k * q ^ i) * star (θ α ^ l) =
        if k * q ^ i ≡ l [MOD q ^ n - 1] then ((q ^ n - 1 : ℕ) : ℂ) else 0 := by
    intro i
    rw [← finsum_mem_coe_finset, ← hS]
    exact (GlobalTheory.T.frobeniusTorus_character_orthogonality F θ hθ n hn).2 _ _
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hc : ((q ^ n - 1 : ℕ) : ℂ) = (q : ℂ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hne : (q : ℂ) ^ n - 1 ≠ 0 := by
    rw [← hc]
    exact_mod_cast hN.ne'
  rw [hc]
  field_simp

end GlobalTheory.CuspGL
end
