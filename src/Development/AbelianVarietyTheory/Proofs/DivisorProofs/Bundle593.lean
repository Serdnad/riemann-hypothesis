module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesCuspidalCharacterGLFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Mathlib.RingTheory.Ideal.Height
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle487
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
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
public import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.FlagDesc

def parAlg (K : Type) [Field K] (a n : ℕ) : Subalgebra K (Matrix (Fin n) (Fin n) K) where
  carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0}
  mul_mem' {M N} hM hN i j hj hi := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : (k : ℕ) < a
    · rw [hM i k hk hi, zero_mul]
    · rw [hN k j hj (not_lt.1 hk), mul_zero]
  add_mem' {M N} hM hN i j hj hi := by
    rw [Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]
  algebraMap_mem' c i j hj hi := by
    have hij : i ≠ j := fun h => by subst h; omega
    simp [Matrix.algebraMap_matrix_apply, hij]

theorem inPar_iff_mem {K : Type} [Field K] {a n : ℕ} (x : GL (Fin n) K) :
    InPar a x ↔ (x : Matrix (Fin n) (Fin n) K) ∈ parAlg K a n := Iff.rfl

theorem inPar_one {K : Type} [Field K] (a n : ℕ) : InPar a (1 : GL (Fin n) K) := by
  intro i j hj hi
  have hij : i ≠ j := fun h => by subst h; omega
  simp [Matrix.one_apply_ne hij]

theorem inPar_mul {K : Type} [Field K] {a n : ℕ} {x z : GL (Fin n) K} (hx : InPar a x) (hz : InPar a z) :
    InPar a (x * z) := by
  rw [inPar_iff_mem, Units.val_mul]
  exact (parAlg K a n).mul_mem hx hz

theorem inPar_inv {K : Type} [Field K] {a n : ℕ} {x : GL (Fin n) K} (h : InPar a x) : InPar a x⁻¹ := by
  have hb : (x : Matrix (Fin n) (Fin n) K).BlockTriangular
      (fun i : Fin n => if a ≤ (i : ℕ) then (1 : ℕ) else 0) := by
    intro i j hij
    apply h i j
    · by_contra hc
      simp only at hij
      split_ifs at hij <;> omega
    · by_contra hc
      simp only at hij
      split_ifs at hij <;> omega
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  apply Matrix.blockTriangular_inv_of_blockTriangular hb
  simp [hi, not_le.2 hj]

theorem conj_adjoin_mem {K : Type} [Field K] {n : ℕ} (B : Subalgebra K (Matrix (Fin n) (Fin n) K))
    (u : GL (Fin n) K) (M X : Matrix (Fin n) (Fin n) K) (hX : X ∈ Algebra.adjoin K {M})
    (hM : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * u ∈ B) :
    ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * X * u ∈ B := by
  induction hX using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hM
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Units.inv_mul]
      exact B.smul_mem B.one_mem r
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact B.add_mem hx hy
  | mul x y _ _ hx hy =>
      have e : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x * y) * u =
          (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * x * u) *
          (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y * u) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [e]; exact B.mul_mem hx hy

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') (i j : Fin n) :
    (galAct F F' n t x : Matrix (Fin n) (Fin n) F') i j = t ((x : Matrix (Fin n) (Fin n) F') i j) := by
  simp [galAct_apply, gal]

theorem incl_coe (n : ℕ) (x : GL (Fin n) F) (i j : Fin n) :
    (incl F F' n x : Matrix (Fin n) (Fin n) F') i j = algebraMap F F' ((x : Matrix (Fin n) (Fin n) F) i j) := by
  simp [incl, gal]

theorem inPar_galAct {a n : ℕ} (t : F' ≃ₐ[F] F') {x : GL (Fin n) F'} (h : InPar a x) :
    InPar a (galAct F F' n t x) := by
  intro i j hj hi
  rw [galAct_coe, h i j hj hi, map_zero]

theorem inPar_incl {a n : ℕ} (x : GL (Fin n) F) : InPar a (incl F F' n x) ↔ InPar a x := by
  constructor
  · intro h i j hj hi
    have := h i j hj hi
    rw [incl_coe] at this
    exact (FaithfulSMul.algebraMap_injective F F') (by rw [this, map_zero])
  · intro h i j hj hi
    rw [incl_coe, h i j hj hi, map_zero]

theorem inPar_nrm {a n : ℕ} (s : F' ≃ₐ[F] F') {x : GL (Fin n) F'} (h : InPar a x) : InPar a (nrm s x) := by
  unfold nrm nrmG
  apply List.prod_induction (fun z => InPar a z)
  · intro u v hu hv; exact inPar_mul hu hv
  · exact inPar_one a n
  · intro z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact inPar_galAct _ h

theorem nrm_one' (s : F' ≃ₐ[F] F') (n : ℕ) : nrm s (1 : GL (Fin n) F') = 1 := by
  unfold nrm nrmG
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact map_one _

end GlobalTheory.Shin.FlagDesc


open GlobalTheory.Shin.FlagDesc in
theorem GlobalTheory.Shin.inPar_twistedConj_iff : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a n : ℕ), a ≤ n → ∀ (γ : GL (Fin n) F) (δ y : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → nrm s δ = incl F F' n γ → (InPar a (y⁻¹ * δ * galAct F F' n s y) ↔ ∃ (y₀ : GL (Fin n) F) (p : GL (Fin n) F'), InPar a p ∧ y = incl F F' n y₀ * p ∧ InPar a (y₀⁻¹ * γ * y₀)) := by
  intro F F' _ _ _ _ s hs a n _ γ δ y hδ hN
  obtain ⟨hfix, -, hconj, -, -⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have hB : ∀ x ∈ parAlg F' a n, x.map s ∈ parAlg F' a n := by
    intro M hM i j hj hi
    simp only [Matrix.map_apply]
    rw [hM i j hj hi, map_zero]
  constructor
  · intro hq
    have hγP : InPar a (y⁻¹ * incl F F' n γ * y) := by
      rw [← hN, ← hconj]; exact inPar_nrm s hq
    have hδP : InPar a (y⁻¹ * δ * y) := by
      rw [inPar_iff_mem, Units.val_mul, Units.val_mul]
      apply conj_adjoin_mem _ y _ _ hδ
      have := (inPar_iff_mem _).1 hγP
      rwa [Units.val_mul, Units.val_mul] at this
    have hεP : InPar a (y⁻¹ * galAct F F' n s y) := by
      have e : y⁻¹ * galAct F F' n s y = (y⁻¹ * δ * y)⁻¹ * (y⁻¹ * δ * galAct F F' n s y) := by group
      rw [e]; exact inPar_mul (inPar_inv hδP) hq
    have hεN : nrm s (y⁻¹ * galAct F F' n s y) = 1 := by
      have := hconj 1 y
      rw [nrm_one', mul_one, inv_mul_cancel] at this
      exact this
    obtain ⟨x, hxB, hε⟩ := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n (parAlg F' a n) hB _ hεP hεN
    have hfx : galAct F F' n s (y * x⁻¹) = y * x⁻¹ := by
      rw [map_mul, map_inv]
      calc galAct F F' n s y * (galAct F F' n s x)⁻¹
          = y * (y⁻¹ * galAct F F' n s y) * (galAct F F' n s x)⁻¹ := by group
        _ = y * (x⁻¹ * galAct F F' n s x) * (galAct F F' n s x)⁻¹ := by rw [hε]
        _ = y * x⁻¹ := by group
    obtain ⟨y₀, hy₀⟩ := (hfix _).1 hfx
    refine ⟨y₀, x, hxB, by rw [hy₀]; group, ?_⟩
    rw [← inPar_incl (F' := F'), map_mul, map_mul, map_inv, hy₀]
    have e : (y * x⁻¹)⁻¹ * incl F F' n γ * (y * x⁻¹) = x * (y⁻¹ * incl F F' n γ * y) * x⁻¹ := by group
    rw [e]
    exact inPar_mul (inPar_mul hxB hγP) (inPar_inv hxB)
  · rintro ⟨y₀, p, hp, rfl, hγ0⟩
    have hs0 : galAct F F' n s (incl F F' n y₀) = incl F F' n y₀ := (hfix _).2 ⟨y₀, rfl⟩
    have e : (incl F F' n y₀ * p)⁻¹ * δ * galAct F F' n s (incl F F' n y₀ * p) =
        p⁻¹ * ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) * galAct F F' n s p := by
      rw [map_mul, hs0]; group
    rw [e]
    have hmid : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
      rw [inPar_iff_mem, Units.val_mul, Units.val_mul]
      apply conj_adjoin_mem _ _ _ _ hδ
      have := (inPar_iff_mem _).1 ((inPar_incl (F' := F') _).2 hγ0)
      rwa [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul] at this
    exact inPar_mul (inPar_mul (inPar_inv hp) hmid) (inPar_galAct s hp)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem card_nrm_one_mul_card_fixed (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (n : ℕ)
    (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) (hB : ∀ x ∈ B, x.map s ∈ B) :
    Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} *
      Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} =
      Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} := by
  obtain ⟨hfix, hinj, hconj, -, -⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have h90 := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n B hB
  have hsB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((galAct F F' n s x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := fun x hx => hB _ hx
  have hinv : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((x⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
    have hx' : x⁻¹ = x ^ (k - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hk, hxk]
    rw [hx', Units.val_pow_eq_pow_val]
    exact pow_mem hx _
  have hmul : ∀ a b : GL (Fin n) F', (a : Matrix (Fin n) (Fin n) F') ∈ B → (b : Matrix (Fin n) (Fin n) F') ∈ B →
      ((a * b : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro a b ha hb
    rw [Units.val_mul]
    exact mul_mem ha hb
  have hn1 : nrm s (1 : GL (Fin n) F') = 1 := by
    unfold nrm nrmG
    apply List.prod_eq_one
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact map_one _
  have hnorm : ∀ x : GL (Fin n) F', nrm s (x⁻¹ * galAct F F' n s x) = 1 := by
    intro x
    have h := hconj 1 x
    rw [mul_one, hn1, mul_one, inv_mul_cancel] at h
    exact h
  let U := {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B}
  let N := {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
  let U₀ := {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
  let φ : U → N := fun x =>
    ⟨x.1⁻¹ * galAct F F' n s x.1, hmul _ _ (hinv _ x.2) (hsB _ x.2), hnorm _⟩
  have hsec : ∀ ε : N, ∃ x : U, φ x = ε := by
    intro ε
    obtain ⟨x, hx, he⟩ := h90 ε.1 ε.2.1 ε.2.2
    exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩
  choose sec hsec using hsec
  have hfixI : ∀ z : GL (Fin n) F, galAct F F' n s (incl F F' n z) = incl F F' n z :=
    fun z => (hfix _).2 ⟨z, rfl⟩
  let f : ∀ ε : N, U₀ → {x : U // φ x = ε} := fun ε z =>
    ⟨⟨incl F F' n z.1 * (sec ε).1, hmul _ _ z.2 (sec ε).2⟩, by
      refine Eq.trans ?_ (hsec ε)
      apply Subtype.ext
      show (incl F F' n z.1 * (sec ε).1)⁻¹ * galAct F F' n s (incl F F' n z.1 * (sec ε).1) =
        (sec ε).1⁻¹ * galAct F F' n s (sec ε).1
      rw [map_mul, hfixI]
      group⟩
  have hbij : ∀ ε : N, Function.Bijective (f ε) := by
    intro ε
    constructor
    · intro z w h
      have h' : incl F F' n z.1 * (sec ε).1 = incl F F' n w.1 * (sec ε).1 :=
        congrArg (fun u : {x : U // φ x = ε} => u.1.1) h
      exact Subtype.ext (hinj (mul_right_cancel h'))
    · rintro ⟨y, hy⟩
      set x := sec ε with hxdef
      have hyx : φ y = φ x := by rw [hy, hsec ε]
      have h1 : y.1⁻¹ * galAct F F' n s y.1 = x.1⁻¹ * galAct F F' n s x.1 :=
        congrArg Subtype.val hyx
      have h2 : galAct F F' n s (y.1 * x.1⁻¹) = y.1 * x.1⁻¹ := by
        rw [map_mul, map_inv]
        calc galAct F F' n s y.1 * (galAct F F' n s x.1)⁻¹
            = y.1 * (y.1⁻¹ * galAct F F' n s y.1) * (galAct F F' n s x.1)⁻¹ := by group
          _ = y.1 * (x.1⁻¹ * galAct F F' n s x.1) * (galAct F F' n s x.1)⁻¹ := by rw [h1]
          _ = y.1 * x.1⁻¹ := by group
      obtain ⟨z, hz⟩ := (hfix _).1 h2
      have hzB : ((incl F F' n z : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
        rw [hz]; exact hmul _ _ y.2 (hinv _ x.2)
      refine ⟨⟨z, hzB⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show incl F F' n z * x.1 = y.1
      rw [hz]; group
  let E : U ≃ N × U₀ := (Equiv.sigmaFiberEquiv φ).symm.trans
    (Equiv.sigmaEquivProdOfEquiv fun ε => (Equiv.ofBijective (f ε) (hbij ε)).symm)
  rw [← Nat.card_prod]
  exact (Nat.card_congr E).symm

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.hyperplaneFixerSumVanishes_cuspidalCharacterGLFiniteField : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, (2 ≤ m ∨ ¬ k ≡ 0 [MOD Nat.card F - 1]) → HFree (cusp θ m k) := by
  first | (exact @GlobalTheory.Shin.hFree_cusp) | (exact GlobalTheory.Shin.hFree_cusp) | (intros; apply GlobalTheory.Shin.hFree_cusp  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.OmLoc

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem pow_smul_d_mem (B : Subalgebra k K) {f v : K} (hf : f ∈ B) (M : ℕ) (hw : v * f ^ M ∈ B) :
    (f ^ (M + M)) • ι1 (D k K v) ∈ omB k K B 1 := by
  have hD : ∀ u ∈ B, ι1 (D k K u) ∈ omB k K B 1 := by
    intro u hu
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, fun _ => u, fun _ => hu, ?_⟩
    rw [one_smul, ExteriorAlgebra.ιMulti_apply]
    simp
  have hc : ∀ c ∈ B, ∀ a ∈ omB k K B 1, c • a ∈ omB k K B 1 := fun c hc a ha =>
    ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B 1 1).2.1 a ha).2.2.2 c hc
  have key : (f ^ (M + M)) • ι1 (D k K v) =
      f ^ M • ι1 (D k K (v * f ^ M)) - (v * f ^ M) • ι1 (D k K (f ^ M)) := by
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_add, smul_smul, smul_smul, pow_add,
      mul_comm (f ^ M) v]
    abel
  rw [key]
  exact sub_mem (hc _ (pow_mem hf M) _ (hD _ hw)) (hc _ hw _ (hD _ (pow_mem hf M)))

end GlobalTheory.PD.OmLoc

namespace GlobalTheory

theorem omB_iff_pow_smul : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ (q : ℕ) (y : DR k K),
      y ∈ omB k K (rB k K x I) q ↔
        ∃ N : ℕ, (algebraMap F K (∏ j ∈ I, x j / x i) ^ N) • y ∈ omB k K (rB k K x {i}) q := by
  intro k _ _ F K _ _ _ _ _ _ d x h I i hi q y
  set f := algebraMap F K (∏ j ∈ I, x j / x i) with hfdef
  obtain ⟨hmono1, -⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h {i} i (Finset.mem_singleton_self i)
  obtain ⟨-, hloc⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h I i hi
  have hBB' : rB k K x {i} ≤ rB k K x I := hmono1 I (Finset.singleton_subset_iff.2 hi)
  have hfB : f ∈ rB k K x {i} := by
    have hz : (∏ j ∈ I, x j / x i) ∈ rA k x {i} :=
      Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
    show IsIntegral (rA k x {i}) f
    exact isIntegral_algebraMap (R := rA k x {i}) (A := K) (x := ⟨_, hz⟩)
  have hf0 : f ≠ 0 :=
    (map_ne_zero (algebraMap F K)).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (h.pd.ne j) (h.pd.ne i))
  have hfinv : f⁻¹ ∈ rB k K x I :=
    (hloc _).2 ⟨1, by rw [pow_one, inv_mul_cancel₀ hf0]; exact Subalgebra.one_mem _⟩
  have hsmul : ∀ (C : Subalgebra k K) (p : ℕ), ∀ c ∈ C, ∀ a ∈ omB k K C p, c • a ∈ omB k K C p :=
    fun C p c hc a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K C p p).2.1 a ha).2.2.2 c hc
  constructor
  · intro hy
    have hQc : ∀ (p : ℕ) (c : K) (z : DR k K), c ∈ rB k K x I →
        (∃ N : ℕ, f ^ N • z ∈ omB k K (rB k K x {i}) p) → ∃ N : ℕ, f ^ N • (c • z) ∈ omB k K (rB k K x {i}) p := by
      rintro p c z hc ⟨N, hN⟩
      obtain ⟨M, hM⟩ := (hloc c).1 hc
      refine ⟨M + N, ?_⟩
      have e : f ^ (M + N) • (c • z) = (c * f ^ M) • (f ^ N • z) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      rw [e]
      exact hsmul _ p _ hM _ hN
    have hQmul : ∀ (p p' : ℕ) (a b : DR k K), (∃ N : ℕ, f ^ N • a ∈ omB k K (rB k K x {i}) p) →
        (∃ N : ℕ, f ^ N • b ∈ omB k K (rB k K x {i}) p') →
        ∃ N : ℕ, f ^ N • (a * b) ∈ omB k K (rB k K x {i}) (p + p') := by
      rintro p p' a b ⟨N, hN⟩ ⟨N', hN'⟩
      refine ⟨N + N', ?_⟩
      have e : f ^ (N + N') • (a * b) = (f ^ N • a) * (f ^ N' • b) := by
        rw [pow_add, mul_smul, smul_mul_assoc, mul_smul_comm]
      rw [e]
      exact (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) p p').1 _ hN _ hN'
    have hQ1 : ∀ v ∈ rB k K x I, ∃ N : ℕ, f ^ N • ι1 (D k K v) ∈ omB k K (rB k K x {i}) 1 := by
      intro v hv
      obtain ⟨M, hM⟩ := (hloc v).1 hv
      exact ⟨M + M, GlobalTheory.PD.OmLoc.pow_smul_d_mem _ hfB M hM⟩
    have hQm : ∀ (n : ℕ) (v : Fin n → K), (∀ j, v j ∈ rB k K x I) →
        ∃ N : ℕ, f ^ N • ExteriorAlgebra.ιMulti K n (fun j => D k K (v j)) ∈ omB k K (rB k K x {i}) n := by
      intro n
      induction n with
      | zero =>
        intro v _
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul, ExteriorAlgebra.ιMulti_zero_apply]
        exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) 0 0).2.2.2 1).2 ⟨1, Subalgebra.one_mem _, (map_one _).symm⟩
      | succ n ih =>
        intro v hv
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        have := hQmul 1 n _ _ (hQ1 (v 0) (hv 0)) (ih (fun j => v j.succ) fun j => hv j.succ)
        rw [Nat.add_comm 1 n] at this
        exact this
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, v, hv, rfl⟩ := hz
      exact hQc q b _ hb (hQm q v hv)
    | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
    | add a c _ _ ha hc =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hc
      refine ⟨N₁ + N₂, ?_⟩
      rw [smul_add]
      apply add_mem
      · rw [pow_add, mul_comm, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₁
      · rw [pow_add, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₂
    | smul r a _ ha =>
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, by rw [smul_comm]; exact Submodule.smul_mem _ r hN⟩
  · rintro ⟨N, hN⟩
    have := hsmul _ q (f⁻¹ ^ N) (pow_mem hfinv N) _
      ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) q q).2.2.1 _ hBB' hN)
    rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_smul] at this

end GlobalTheory
end
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem heightOne_eq_span_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∃ t : A, Irreducible t ∧ p = Ideal.span {t} := by
  intro k F _ _ _ d u hu A hA p hp hh
  subst hA
  haveI := hp
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (Set.range u)) :=
    hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
  refine ⟨g, ?_, hg⟩
  have hne : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot_of_height_eq_one hh (by rw [hg]; simp)
  rw [hg] at hp
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

theorem mem_traceDual_localization_iff_forall_regularForm : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ p hp hh z
  obtain ⟨t, ht, hpt⟩ := heightOne_eq_span_irreducible k F d u hu A hA p hp hh
  have h2 : ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 :=
    fun Q hQ hov => GlobalTheory.T.height_eq_one_of_liesOver_height_one k F K A B hB p hp hh Q hQ hov
  have h3 := fun Q hQ hov => GlobalTheory.T.exists_uniformizer_ramification_of_height_one k F K d u hu A hA B hB p hp t ht hpt Q hQ (h2 Q hQ hov) hov
  rw [GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt k F K d u hu A hA B hB p hp hh t ht hpt h2 h3 z]
  constructor
  · intro hl Q hQ hov
    obtain ⟨s, e, he, hs, hun, htd⟩ := h3 Q hQ hov
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mpr
      (hl Q hQ hov s e he hs hun htd)
  · intro hr Q hQ hov s e he hs hun htd
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mp (hr Q hQ hov)

end GlobalTheory
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ a, ghost p O 0 a = WittVector.fontaineTheta O p a) ∧ (∀ n a, ghost p O n (ofPadic p O a) = padicToO p O a) ∧ (∀ n, ghost p O n (Sandwich.mu ε) = 0) ∧ ghost p O 0 (xi ε) = 0 ∧ (∀ n, ghost p O (n + 1) (xi ε) = p) ∧ ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a := by
  first | exact @GlobalTheory.PDivLat.ghost_values | exact GlobalTheory.PDivLat.ghost_values | (intros; apply GlobalTheory.PDivLat.ghost_values <;> assumption)
end
