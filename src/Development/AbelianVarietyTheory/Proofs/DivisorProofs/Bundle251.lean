module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
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
public import Mathlib.Data.Nat.Prime.Factorial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_inv_signFactorial {E : Type} [AddCommGroup E] (p : ℕ) [hp : Fact p.Prime]
    (hE : ∀ x : E, p • x = 0) (a : ℕ) (ha : a < p) :
    ∃ u : ℤ, ∀ y : E, (u * ((-1 : ℤ) ^ a * (a.factorial : ℤ))) • y = y := by
  have hcop : IsCoprime ((-1 : ℤ) ^ a * (a.factorial : ℤ)) (p : ℤ) := by
    apply IsCoprime.mul_left
    · exact IsCoprime.pow_left (isCoprime_one_left.neg_left)
    · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
        (fun h => absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (by omega)))
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u, fun y => ?_⟩
  have h1 : u * ((-1 : ℤ) ^ a * (a.factorial : ℤ)) = 1 - v * p := by linarith
  rw [h1, sub_smul, one_smul, mul_smul, natCast_zsmul, hE, smul_zero, sub_zero]

theorem cartierAt_signFactorial : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E)
    (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) →
    (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  intro E _ p hp d γ γ' N T hE hN hγ hC
  have hp0 : 0 < p := hp.out.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx h0
    rw [hγ 0 x hx] at h0
    simp at h0
    exact hC.inj_zero x hx h0
  · intro a x hx z hz h
    by_cases hpa : p ≤ a + 1
    · rw [hN _ hpa] at hx; exact (AddSubgroup.mem_bot.1 hx)
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      apply hC.inj_succ a x hx (u • z) (AddSubgroup.zsmul_mem _ hz u)
      rw [hγ _ x hx] at h
      rw [map_zsmul, ← h, ← mul_smul, hu]
  · intro y hy hd
    obtain ⟨x, hx, rfl⟩ := hC.surj_zero y hy hd
    exact ⟨x, hx, by rw [hγ 0 x hx]; simp⟩
  · intro a y hy hd
    obtain ⟨x, hx, z, hz, rfl⟩ := hC.surj_succ a y hy hd
    by_cases hpa : p ≤ a + 1
    · have hx0 : x = 0 := by rw [hN _ hpa] at hx; exact AddSubgroup.mem_bot.1 hx
      subst hx0
      refine ⟨0, AddSubgroup.zero_mem _, z, hz, ?_⟩
      rw [hγ (a + 1) 0 (AddSubgroup.zero_mem _)]; simp
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      refine ⟨u • x, AddSubgroup.zsmul_mem _ hx u, z, hz, ?_⟩
      rw [hγ _ _ (AddSubgroup.zsmul_mem _ hx u), map_zsmul, ← mul_smul, mul_comm, hu]

end GlobalTheory.DI
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.TorsMem

private theorem div_N_mem_tauPair_lattice_iff_dvd (N : ℕ) [NeZero N] (τ : ℍ) (a b : ℤ) :
    ((a : ℂ) * τ + (b : ℂ)) / N ∈ (tauPair τ).lattice ↔ (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    rw [h1, h2, eq_div_iff hN] at h
    obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.mp (tauPair τ).indep
      (((N : ℤ) * m - a : ℤ) : ℝ) (((N : ℤ) * n - b : ℤ) : ℝ) (by
        rw [h1, h2, Complex.real_smul, Complex.real_smul]
        push_cast
        linear_combination h)
    norm_cast at k1 k2
    exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    refine ⟨m, n, ?_⟩
    rw [h1, h2, eq_div_iff hN]
    push_cast
    ring

theorem div_mem_iff (N : ℕ) [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + (v : ℂ)) / N ∈ (tauPair τ).lattice ↔ (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by
  rw [div_N_mem_tauPair_lattice_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  intro N _ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : ∀ x : Fin 2 → ZMod N,
      tors N τ x = ((((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ)) / N := by
    intro x
    simp only [tors, Int.cast_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have e : tors N τ x - tors N τ y = (((((x 0).val : ℤ) - (y 0).val : ℤ) : ℂ) * τ
        + ((((x 1).val : ℤ) - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht]; push_cast; ring
    rw [e, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp [sub_eq_zero]
  · intro x y
    have e : tors N τ (x + y) - (tors N τ x + tors N τ y) =
        (((((x + y) 0).val : ℤ) - (x 0).val - (y 0).val : ℤ) * (τ : ℂ)
        + (((((x + y) 1).val : ℤ) - (x 1).val - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht, ht]; push_cast; ring
    rw [e, div_mem_iff]
    simp
  · intro x
    rw [ht, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp
  · intro x
    rw [PeriodPair.mem_lattice]
    refine ⟨(x 0).val, (x 1).val, ?_⟩
    change (((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ) * 1 = _
    rw [ht]
    field_simp
  · intro z hz
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hz
    change (m : ℂ) * τ + n * 1 = N * z at h
    refine ⟨![(m : ZMod N), (n : ZMod N)], ?_⟩
    have hz' : z = ((m : ℂ) * τ + (n : ℂ)) / N := by
      rw [eq_div_iff hN]
      linear_combination -h
    have e : z - tors N τ ![(m : ZMod N), (n : ZMod N)] =
        (((m - ((m : ZMod N)).val : ℤ) : ℂ) * τ + ((n - ((n : ZMod N)).val : ℤ) : ℂ)) / N := by
      rw [hz', ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    rw [e, div_mem_iff]
    simp

end GlobalTheory.WpFam.TorsMem
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NrmBasic

section General

variable {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ)

theorem nrmG_zero (δ : G) : nrmG φ s 0 δ = 1 := by
  simp [nrmG]

theorem nrmG_succ (l : ℕ) (δ : G) : nrmG φ s (l + 1) δ = nrmG φ s l δ * φ (s ^ l) δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem nrmG_twConj (l : ℕ) (δ y : G) :
    nrmG φ s l (y⁻¹ * δ * φ s y) = y⁻¹ * nrmG φ s l δ * φ (s ^ l) y := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, ih]
    have h1 : φ (s ^ l) (y⁻¹ * δ * φ s y) = (φ (s ^ l) y)⁻¹ * φ (s ^ l) δ * φ (s ^ (l + 1)) y := by
      rw [map_mul, map_mul, map_inv, pow_succ, map_mul, MulAut.mul_apply]
    rw [h1]
    group

theorem mul_map_nrmG (l : ℕ) (δ : G) :
    δ * φ s (nrmG φ s l δ) = nrmG φ s l δ * φ (s ^ l) δ := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, map_mul, ← mul_assoc, ih, pow_succ', map_mul, MulAut.mul_apply]

theorem nrmG_mul (l : ℕ) (δ ε : G) (h : ∀ i j : ℕ, Commute (φ (s ^ i) δ) (φ (s ^ j) ε)) :
    nrmG φ s l (δ * ε) = nrmG φ s l δ * nrmG φ s l ε := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, nrmG_succ, ih, map_mul]
    have hc : Commute (nrmG φ s l ε) (φ (s ^ l) δ) := by
      unfold nrmG
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (h l i).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (nrmG φ s l ε), hc.eq, mul_assoc]

end General

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem pow_finrank_eq_one (s : F' ≃ₐ[F] F') : s ^ Module.finrank F F' = 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

theorem fixed_iff (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    s x = x ↔ x ∈ Set.range (algebraMap F F') := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, ← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro t _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hs t)
    have h1 : ∀ m : ℕ, (s ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    have h2 : ∀ m : ℕ, (s⁻¹ ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply]
        have : s⁻¹ x = x := by
          conv_lhs => rw [← hx]
          exact s.symm_apply_apply x
        rw [this, ih]
    cases k with
    | ofNat m => simpa using h1 m
    | negSucc m => rw [zpow_negSucc, ← inv_pow]; exact h2 (m + 1)
  · rintro ⟨a, rfl⟩
    exact s.commutes a

end Fields

theorem main : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  intro F F' _ _ _ _ s hs n
  have hl := pow_finrank_eq_one s
  have hinj : Function.Injective (algebraMap F F') := (algebraMap F F').injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have he : ∀ i j, s ((x : Matrix (Fin n) (Fin n) F') i j) = (x : Matrix (Fin n) (Fin n) F') i j := by
        intro i j
        have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hx
        simpa [galAct_apply, gal] using this
      choose M0 hM using fun i j => (fixed_iff s hs _).1 (he i j)
      let M : Matrix (Fin n) (Fin n) F := Matrix.of M0
      have hdet : (algebraMap F F') (M.det) = (x : Matrix (Fin n) (Fin n) F').det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        exact hM i j
      have hu : IsUnit M := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        intro h0
        have : (x : Matrix (Fin n) (Fin n) F').det = 0 := by rw [← hdet, h0, map_zero]
        exact (Matrix.GeneralLinearGroup.det_ne_zero x) this
      refine ⟨hu.unit, ?_⟩
      ext i j
      simp [incl, gal, M, hM]
    · rintro ⟨y, rfl⟩
      ext i j
      simp [galAct_apply, gal, incl]
  · intro a b hab
    ext i j
    have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hab
    exact hinj (by simpa [incl, gal] using this)
  · intro δ y
    unfold nrm
    rw [nrmG_twConj, hl, map_one, MulAut.one_apply]
  · intro δ
    unfold nrm
    rw [mul_map_nrmG, hl, map_one, MulAut.one_apply]
  · intro δ ε h
    unfold nrm
    exact nrmG_mul _ _ _ _ _ fun i j => h _ _

end GlobalTheory.Shin.NrmBasic

end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HcGal

variable {F F' : Type} [Field F] [Field F']

theorem gal_coe (t : F →+* F') {n : ℕ} (x : GL (Fin n) F) :
    ((gal t n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = (x : Matrix (Fin n) (Fin n) F).map t := by
  ext i j; simp [gal]

theorem gal_id {n : ℕ} (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem ent_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem isUnit_map_iff (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map t) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  have : (M.map t).det = t M.det := by
    rw [RingHom.map_det]; rfl
  rw [this, _root_.map_ne_zero]

theorem toG_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map t) = gal t n (toG M) := by
  unfold toG
  by_cases h : IsUnit M
  · rw [dite_eq_left h, dite_eq_left ((isUnit_map_iff t M).2 h)]
    apply Units.ext
    rw [gal_coe, IsUnit.unit_spec, IsUnit.unit_spec]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ((isUnit_map_iff t M).1 h')), map_one]

theorem tlG_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (gal t n x) = gal t a (tlG a x) := by
  unfold tlG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [tl, Matrix.map_apply, ent_map]

theorem brG_gal (t : F →+* F') (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (gal t n x) = gal t b (brG a b x) := by
  unfold brG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [br, Matrix.map_apply, ent_map]

theorem inPar_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (gal t n x) ↔ InPar a x := by
  unfold InPar
  simp only [gal_coe, Matrix.map_apply, map_eq_zero]

theorem gal_bijective (t : F ≃+* F') (n : ℕ) : Function.Bijective (gal (t : F →+* F') n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨gal (t.symm : F' →+* F) n, fun x => ?_, fun x => ?_⟩
  · ext i j; simp [gal]
  · ext i j; simp [gal]

theorem hc_gal : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) =
    hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  intro F _ _ t a b n α β x
  unfold hc hcTw
  congr 1
  symm
  refine finsum_eq_of_bijective (gal (t : F →+* F) n) (gal_bijective t n) fun y => ?_
  rw [gal_id, gal_id, ← map_inv, ← map_mul, ← map_mul, tlG_gal, brG_gal]
  simp only [inPar_gal]

end GlobalTheory.Shin.HcGal
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

section LogMul

variable {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K)
  {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (A : Subring K)

omit [Fact p.Prime] in
lemma logLift_pp_zero (hπ : IsFlatLift p π) : (p : Kt) * p = 0 := by
  rw [hπ.ann]; simp [map_natCast, CharP.cast_eq_zero]

omit [Fact p.Prime] in
lemma logLift_one : LogLift p π F s (A : Set K) 1 :=
  ⟨1, map_one π, fun i _ => ⟨0, by simp [A.zero_mem], by simp⟩⟩

omit [Fact p.Prime] in
lemma logLift_mul (hπ : IsFlatLift p π) {g g' : K} (hg : LogLift p π F s (A : Set K) g)
    (hg' : LogLift p π F s (A : Set K) g') : LogLift p π F s (A : Set K) (g * g') := by
  obtain ⟨z, hz, hF⟩ := hg
  obtain ⟨z', hz', hF'⟩ := hg'
  have hpp := logLift_pp_zero p π hπ
  refine ⟨z * z', by simp [hz, hz'], fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  obtain ⟨w', hw', hFw'⟩ := hF' i hi
  refine ⟨w + w', by rw [map_add (f := _)]; exact A.add_mem hw hw', ?_⟩
  rw [map_mul, hFw, hFw', mul_pow]
  linear_combination (z ^ p * z' ^ p * w * w') * hpp

omit [Fact p.Prime] in
lemma logLift_inv (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    LogLift p π F s (A : Set K) g⁻¹ := by
  obtain ⟨z, hz, hF⟩ := hg
  have hpp := logLift_pp_zero p π hπ
  have hπp : π (p : Kt) = 0 := by simp [map_natCast, CharP.cast_eq_zero]
  obtain ⟨z', hz'⟩ := hπ.surj g⁻¹
  obtain ⟨e, he⟩ := (hπ.ker (z * z' - 1)).1 (by simp [hz, hz', hg0])
  set u := z' * (1 - p * e) with hu
  have hzu : z * u = 1 := by
    have : z * z' = 1 + p * e := by linear_combination he
    rw [hu, ← mul_assoc, this]; linear_combination (-(e * e)) * hpp
  have hπu : π u = g⁻¹ := by simp [hu, hz', hπp]
  clear_value u
  refine ⟨u, hπu, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  refine ⟨-w, by rw [map_neg]; exact A.neg_mem hw, ?_⟩
  have h1 : F i z * F i u = 1 := by rw [← map_mul, hzu, map_one]
  have h2 : F i z * (u ^ p * (1 + p * -w)) = 1 := by
    rw [hFw]
    have : z ^ p * u ^ p = 1 := by rw [← mul_pow, hzu, one_pow]
    linear_combination (1 - (p:Kt) * w * ((p:Kt) * w)) * this - (w * w) * hpp
  linear_combination (u ^ p * (1 + p * -w)) * h1 - (F i u) * h2

omit [Fact p.Prime] in
lemma logLift_zpow (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    ∀ n : ℤ, LogLift p π F s (A : Set K) (g ^ n) := by
  have hpow : ∀ {h : K}, LogLift p π F s (A : Set K) h → ∀ k : ℕ, LogLift p π F s (A : Set K) (h ^ k) := by
    intro h hh k
    induction k with
    | zero => simpa using logLift_one p π F s A
    | succ k ih => rw [pow_succ]; exact logLift_mul p π F s A hπ ih hh
  intro n
  cases n with
  | ofNat k => rw [Int.ofNat_eq_coe, zpow_natCast]; exact hpow hg k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow]
    exact hpow (logLift_inv p π F s A hπ hg0 hg) (k + 1)

end LogMul

end GlobalTheory.DI
end
