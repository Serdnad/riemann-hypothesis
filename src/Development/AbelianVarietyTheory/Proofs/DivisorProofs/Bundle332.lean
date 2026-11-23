module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.galoisTwistedNormGL_basic_properties : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  first | (exact @GlobalTheory.Shin.NrmBasic.main) | (exact GlobalTheory.Shin.NrmBasic.main) | (intros; apply GlobalTheory.Shin.NrmBasic.main  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) = hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  first | (exact @GlobalTheory.Shin.HcGal.hc_gal) | (exact GlobalTheory.Shin.HcGal.hc_gal) | (intros; apply GlobalTheory.Shin.HcGal.hc_gal  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.BlocksTwist

theorem toG_map {F : Type} [Field F] (t : F →+* F) {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) :
    toG (M.map t) = gal t m (toG M) := by
  have h' : IsUnit (M.map t) := by simpa using h.map (t.mapMatrix)
  unfold toG
  rw [dite_eq_left h', dite_eq_left h]
  ext i j
  simp [gal]

theorem coe_gal {F : Type} [Field F] (t : F →+* F) (n : ℕ) (p : GL (Fin n) F) :
    ((gal t n p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (p : Matrix (Fin n) (Fin n) F).map t := by
  simp [gal]

theorem ent_map {F : Type} [Field F] (t : F →+* F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem tl_map {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j; simp [tl, ent_map]

theorem br_map {F : Type} [Field F] (t : F →+* F) (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j; simp [br, ent_map]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (p : GL (Fin n) F) (hp : InPar a p) :
    InPar a (gal t n p) := by
  intro i j hj hi
  rw [coe_gal]
  simp [hp i j hj hi]

theorem blocks_twist : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  intro F _ t a b n hn p x hp hx
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := BlockPar.block_par F a b n hn
  let p' : H := ⟨p, (hH p).2 hp⟩
  let x' : H := ⟨x, (hH x).2 hx⟩
  let g' : H := ⟨gal t n p, (hH _).2 (inPar_gal t a p hp)⟩
  have key : π (p'⁻¹ * x' * g') = (π p')⁻¹ * π x' * π g' := by simp only [map_mul, map_inv]
  rw [hπ, hπ, hπ, hπ] at key
  have e : ((p'⁻¹ * x' * g' : H) : GL (Fin n) F) = p⁻¹ * x * gal t n p := rfl
  rw [e] at key
  have htl : tlG a (gal t n p) = gal t a (tlG a p) := by
    subst hn
    unfold tlG
    rw [coe_gal, tl_map, toG_map _ _ (BlockPar.units_of_par p hp).1]
  have hbr : brG a b (gal t n p) = gal t b (brG a b p) := by
    subst hn
    unfold brG
    rw [coe_gal, br_map, toG_map _ _ (BlockPar.units_of_par p hp).2]
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at key
  rw [← htl, ← hbr]
  exact key

end GlobalTheory.Shin.BlocksTwist
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  first | (exact @GlobalTheory.Shin.BlockPar.block_par) | (exact GlobalTheory.Shin.BlockPar.block_par) | (intros; apply GlobalTheory.Shin.BlockPar.block_par  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraInductionGL_one_left_right_unit : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α → hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  first | (exact @GlobalTheory.Shin.HcUnit.main) | (exact GlobalTheory.Shin.HcUnit.main) | (intros; apply GlobalTheory.Shin.HcUnit.main  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem liftL_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → 0 < l →
    (∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2) →
    deg (liftL q l L) = deg L ∧ ∀ p ∈ liftL q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftL, deg]
  | cons p L ih =>
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2 := fun p' hp' => hL p' (List.mem_cons_of_mem _ hp')
    obtain ⟨ihd, ihm⟩ := ih hL'
    obtain ⟨hp0, hpd, hpr⟩ := hL p List.mem_cons_self
    obtain ⟨c, hc⟩ := hpd
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have hdiv : p.1 / l = c := by rw [hc]; exact Nat.mul_div_cancel_left c hl
    have hcons : liftL q l (p :: L) = (List.range l).map (fun i => (p.1 / l, p.2 * q ^ i)) ++ liftL q l L := by
      simp [liftL, List.flatMap_cons]
    refine ⟨?_, ?_⟩
    · rw [hcons]
      simp only [deg, List.map_append, List.sum_append, List.map_map] at ihd ⊢
      rw [ihd]
      simp [Function.comp_def, List.sum_replicate, hdiv, hc, Nat.mul_div_cancel_left c hl]
    · intro p' hp'
      rw [hcons, List.mem_append] at hp'
      rcases hp' with hp' | hp'
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp'
        refine ⟨by simpa [hdiv] using hc0, ?_⟩
        simp only [hdiv]
        rw [hc] at hpr
        exact (GlobalTheory.Shin.reg_step_of_dvd q l c p.2 hq hl hc0 hpr).1 i
      · exact ihm p' hp'

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.inPar_conj_of_mem_adjoin_incl_of_inPar_conj : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → InPar a (y₀⁻¹ * γ * y₀) → InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
  first | (exact @GlobalTheory.adjoin_conj_inPar) | (exact GlobalTheory.adjoin_conj_inPar) | (intros; apply GlobalTheory.adjoin_conj_inPar <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.regular_pair_lift_to_prime_power_field : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧ ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  first | (exact @GlobalTheory.Shin.reg_norm_frob) | (exact GlobalTheory.Shin.reg_norm_frob) | (intros; apply GlobalTheory.Shin.reg_norm_frob  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.galoisTwistedNormGL_diagonal_blocks : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (γ : GL (Fin n) F) (δ : GL (Fin n) F'), InPar a γ → InPar a δ → nrm s δ = incl F F' n γ → nrm s (tlG a δ) = incl F F' a (tlG a γ) ∧ nrm s (brG a b δ) = incl F F' b (brG a b γ) := by
  first | (exact @GlobalTheory.ShinBlock.nrm_blocks) | (exact GlobalTheory.ShinBlock.nrm_blocks) | (intros; apply GlobalTheory.ShinBlock.nrm_blocks <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity : ∀ (N : ℕ) (y : Fin 2 → ZMod N) (τ : ℍ), ((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y τ = -(G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) := by
  first | exact @GlobalTheory.wB_nonhol_correction | exact GlobalTheory.wB_nonhol_correction | (intros; apply GlobalTheory.wB_nonhol_correction <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma one_sub_mul_sum_range_natCast_mul_pow_add (x : ℂ) (n : ℕ) :
    (1 - x) * ∑ i ∈ Finset.range n, (i : ℂ) * x ^ i + n * x ^ n =
      ∑ i ∈ Finset.range n, x ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    push_cast
    ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one (ζ : ℂ) (M : ℕ) (hζ : IsIntegral ℤ ζ)
    (hM : ζ ^ M = 1) (h1 : ζ ≠ 1) : IsIntegral ℤ ((M : ℂ) / (1 - ζ)) := by
  have hsub : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hgeom : ∑ i ∈ Finset.range M, ζ ^ (i + 1) = 0 := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, geom_sum_eq h1, hM, sub_self, zero_div, zero_mul]
  have key := one_sub_mul_sum_range_natCast_mul_pow_add ζ M
  rw [hgeom, hM, mul_one] at key
  have hq : (M : ℂ) / (1 - ζ) = -∑ i ∈ Finset.range M, (i : ℂ) * ζ ^ i := by
    rw [div_eq_iff hsub]
    linear_combination key
  rw [hq]
  exact (IsIntegral.sum _ fun i _ => (isIntegral_natCast i).mul (hζ.pow i)).neg


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.isIntegral_coefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ),
    0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cP N x k) ∧
      IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
  intro N _ M x k _ hx
  obtain ⟨-, -, hzero, -, hpow, -, -, hint⟩ :=
    _root_.GlobalTheory.WpFam.AddCharZMod.main N
  have h12 : IsIntegral ℤ (12 : ℂ) := by simpa using isIntegral_natCast (R := ℤ) (B := ℂ) 12
  have htw : ∀ (a : ℕ) (s : ℂ), IsIntegral ℤ s →
      IsIntegral ℤ (_root_.GlobalTheory.WpFam.cSum N a s x k) := by
    intro a s hs
    unfold _root_.GlobalTheory.WpFam.cSum
    refine IsIntegral.sum _ fun m _ => ((isIntegral_natCast m).pow a).mul ?_
    refine IsIntegral.add ?_ (hs.mul ?_)
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
  have hG : IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
    unfold _root_.GlobalTheory.WpFam.cG
    split_ifs
    · rw [show (12 : ℂ) * (-1 / 12) = -1 by norm_num]
      exact isIntegral_one.neg
    · exact h12.mul ((isIntegral_natCast 2).mul (isIntegral_natCast _))
    · simp [isIntegral_zero]
  have hB : IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) := by
    unfold _root_.GlobalTheory.WpFam.cB _root_.GlobalTheory.WpFam.cD
    split_ifs with hk h0
    · by_cases h1 : _root_.GlobalTheory.WpFam.ch N (x 1) = 1
      · simp [h1, isIntegral_zero]
      · have hζM : _root_.GlobalTheory.WpFam.ch N (x 1) ^ M = 1 := by
          have hx1 := congr_fun hx 1
          simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hx1
          rw [← hpow, hx1, hzero]
        have hq := isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one _ M (hint (x 1)) hζM h1
        constructor
        · rw [show (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.ch N (x 1) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 2)
              = _root_.GlobalTheory.WpFam.ch N (x 1) * ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 2 by
              rw [div_pow]; ring]
          exact (hint _).mul (hq.pow 2)
        · rw [show (M : ℂ) ^ 3 * (_root_.GlobalTheory.WpFam.ch N (x 1) * (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) /
              (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 3) = _root_.GlobalTheory.WpFam.ch N (x 1) *
              (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) *
              ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 3 by rw [div_pow]; ring]
          exact ((hint _).mul (isIntegral_one.add (hint _))).mul (hq.pow 3)
    · simp [isIntegral_zero]
    · exact ⟨((isIntegral_natCast M).pow 2).mul (htw 1 1 isIntegral_one),
        ((isIntegral_natCast M).pow 3).mul (htw 2 (-1) isIntegral_one.neg)⟩
  refine ⟨hB.1, hB.2, ?_, hG⟩
  unfold _root_.GlobalTheory.WpFam.cP
  split_ifs
  · simp [isIntegral_zero]
  · rw [show 12 * (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.cB N x k - _root_.GlobalTheory.WpFam.cG N k)
        = 12 * ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) -
          (M : ℂ) ^ 2 * (12 * _root_.GlobalTheory.WpFam.cG N k) by ring]
    exact (h12.mul hB.1).sub (((isIntegral_natCast M).pow 2).mul hG)

end GlobalTheory.WpFam
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.CoeffConj

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem vmul_dg_apply_zero_and_one {N : ℕ} (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ) :
    _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 0 = x 0 ∧
      _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 1 = (a : ZMod N) * x 1 := by
  simp [_root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cG_eq (N : ℕ) (g : ℂ ≃+* ℂ) (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k := by
  unfold _root_.GlobalTheory.WpFam.cG
  split_ifs <;> simp [map_ofNat]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cSum_eq_cSum_vmul_dg (N : ℕ) (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ)
    (hg : _root_.GlobalTheory.WpFam.ZetaAct g N a) (e : ℕ) (s : ℂ) (hs : g s = s) (x : Fin 2 → ZMod N)
    (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cSum N e s x k) =
      _root_.GlobalTheory.WpFam.cSum N e s (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hg
  unfold _root_.GlobalTheory.WpFam.cSum

  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h0, h1]
  simp only [map_mul, map_pow, map_natCast, map_add (f := _), apply_ite g, map_zero, hs, hg]
  rw [mul_neg, mul_left_comm (a : ZMod N)]


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.CoeffConj.main : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ (x : Fin 2 → ZMod N) (k : ℕ), g (_root_.GlobalTheory.WpFam.cB N x k) = _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cD N x k) = _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k ∧ g (_root_.GlobalTheory.WpFam.cP N x k) = _root_.GlobalTheory.WpFam.cP N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  intro N _ g a hg x k
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  have hζ := hg
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hζ
  have hG := ringEquiv_cG_eq N g k
  have hB : g (_root_.GlobalTheory.WpFam.cB N x k) =
      _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cB
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 1 1 (map_one g) x k
  have hD : g (_root_.GlobalTheory.WpFam.cD N x k) =
      _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cD
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_add (f := _), map_mul, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 2 (-1) (by simp) x k
  refine ⟨hB, hD, hG, ?_⟩
  have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
  unfold _root_.GlobalTheory.WpFam.cP
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos (hzero.2 hx), map_zero]
  · have hx' : _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) ≠ 0 := fun h => hx (hzero.1 h)
    simp only [hx, hx', if_false, map_sub, hB, hG]

end GlobalTheory.WpFam.CoeffConj
end
