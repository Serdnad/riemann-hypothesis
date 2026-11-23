module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle139
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLevi
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle144
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Formalism.L2.DIV GlobalTheory.FinGL.Bruhat
open scoped Classical

namespace GlobalTheory.GLm.Shuffle

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem pm_eq_mono (σ : Equiv.Perm (Fin n)) : (pm g σ : Mt g n) = mono (σ, fun _ => 1) := by
  have hm : (fun r j : Fin n => if r = σ j then (1 : ZMod g) else 0) = mono (σ, fun _ => (1 : (ZMod g)ˣ)) := by
    ext r j; simp [mono]
  have hu : IsUnit (mono (F := ZMod g) (σ, fun _ => (1 : (ZMod g)ˣ))) := by
    refine IsUnit.of_mul_eq_one (mono (σ.symm, fun _ => (1 : (ZMod g)ˣ))) ?_
    ext r j
    rw [mul_mono]
    simp [mono, Matrix.one_apply]
  unfold pm toG
  rw [hm, dite_eq_left hu]
  rfl

theorem isUniUp_iff (u : Gn g n) : IsUniUp (u : Mt g n) ↔ u ∈ unip (ZMod g) n :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩,
    fun h a b => ⟨fun hab => unip_lower h hab, fun e => e ▸ unip_diag h a⟩⟩

theorem inPar_iff (a : ℕ) (p : Gn g n) :
    InPar a (p : Mt g n) ↔ p ∈ blockTri (κ := ZMod g) (fun i : Fin n => if (i : ℕ) < a then 0 else 1 : Fin n → ℕ) := by
  rw [mem_blockTri]
  constructor
  · intro h i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at hij
    exact h i j hj (not_lt.1 hi)
  · intro h i j hj hi
    exact h i j (by simp [hj, not_lt.2 hi])

theorem block_of_eq {a : ℕ} {σ σ' : Equiv.Perm (Fin n)} {u u' p p' : Gn g n} (hu : IsUniUp (u : Mt g n))
    (hu' : IsUniUp (u' : Mt g n)) (hp : InPar a (p : Mt g n)) (hp' : InPar a (p' : Mt g n))
    (h : u * pm g σ * p = u' * pm g σ' * p') (r : Fin n) (hr : (σ.symm r : ℕ) < a) : (σ'.symm r : ℕ) < a := by
  have hv : u'⁻¹ * u ∈ unip (ZMod g) n :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ((isUniUp_iff _).1 hu')) ((isUniUp_iff _).1 hu)
  have hq : InPar a ((p' * p⁻¹ : Gn g n) : Mt g n) :=
    (inPar_iff _ _).2 (Subgroup.mul_mem _ ((inPar_iff _ _).1 hp') (Subgroup.inv_mem _ ((inPar_iff _ _).1 hp)))
  have h1 : (u'⁻¹ * u) * pm g σ = pm g σ' * (p' * p⁻¹) := by
    calc (u'⁻¹ * u) * pm g σ = u'⁻¹ * (u * pm g σ * p) * p⁻¹ := by group
      _ = _ := by rw [h]; group
  have h2 := congrFun (congrFun (congrArg (fun z : Gn g n => (z : Mt g n)) h1) r) (σ.symm r)
  rw [Units.val_mul _ (pm g σ), Units.val_mul (pm g σ'), pm_eq_mono, pm_eq_mono, mul_mono, mono_mul] at h2
  simp only [Equiv.apply_symm_apply, Units.val_one, mul_one, one_mul] at h2
  rw [unip_diag hv] at h2
  by_contra hc
  rw [hq _ _ hr (not_lt.1 hc)] at h2
  exact one_ne_zero h2

noncomputable def key (S : Fin n → Prop) (r : Fin n) : ℕ := if S r then (r : ℕ) else n + r

theorem key_injective (S : Fin n → Prop) : Function.Injective (key S) := by
  intro r s h
  have := r.2; have := s.2
  unfold key at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem key_mono {a : ℕ} {σ : Equiv.Perm (Fin n)} {S : Fin n → Prop} (hS : ∀ r, S r ↔ (σ.symm r : ℕ) < a)
    (hσ : ∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) : Monotone (key S ∘ σ) := by
  refine StrictMono.monotone fun i j hij => ?_
  have h1 := hσ i j hij
  have h2 : (i : ℕ) < j := hij
  have := (σ i).2
  simp only [Function.comp, key, hS, Equiv.symm_apply_apply, Fin.lt_def] at h1 ⊢
  split_ifs <;> omega

theorem exists_shuffle {a : ℕ} (ha : a ≤ n) (s : Equiv.Perm (Fin n)) : ∃ σ : Equiv.Perm (Fin n),
    (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧
      ∀ j : Fin n, (s.symm (σ j) : ℕ) < a ↔ (j : ℕ) < a := by
  set S : Fin n → Prop := fun r => (s.symm r : ℕ) < a with hS
  set σ := Tuple.sort (key S) with hσ
  have hm : Monotone (key S ∘ σ) := Tuple.monotone_sort _
  have hlt : ∀ r, key S r < n ↔ S r := by
    intro r
    have := r.2
    unfold key
    split_ifs with h <;> simp [h]
  have hcard : (Finset.univ.filter fun i => (key S ∘ σ) i < n).card = a := by
    have : (Finset.univ.filter fun i : Fin n => (i : ℕ) < a).card = a := by
      rw [Fin.card_filter_val_lt]; omega
    rw [← this]
    refine Finset.card_equiv (σ.trans s.symm) fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    exact hlt _
  have hiff : ∀ j : Fin n, S (σ j) ↔ (j : ℕ) < a := by
    intro j
    rw [← hlt, ← hcard]
    exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone hm).symm
  refine ⟨σ, fun i j hij hb => ?_, hiff⟩
  have h1 : (key S ∘ σ) i < (key S ∘ σ) j :=
    (hm.strictMono_of_injective ((key_injective S).comp σ.injective)) hij
  have h2 : (i : ℕ) < j := hij
  simp only [Function.comp, key, hiff] at h1
  rw [Fin.lt_def]
  split_ifs at h1 <;> omega

theorem existsUnique_shuffle : ∀ (g : ℕ) [Fact g.Prime] (a n : ℕ), a ≤ n → ∀ x : Gn g n, ∃! σ : Equiv.Perm (Fin n), (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧ ∃ u p : Gn g n, IsUniUp (u : Mt g n) ∧ InPar a (p : Mt g n) ∧ x = u * pm g σ * p := by
  intro g _ a n ha x
  obtain ⟨m, u, hu, u', hu', hx⟩ := exists_decomp x
  obtain ⟨σ, hσ, hb⟩ := exists_shuffle ha m.1
  have hp : InPar a (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) := by
    intro i j hj hi
    have h1 : (pm g σ : Mt g n) * (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) = mono m * (u' : Mt g n) := by
      rw [← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, hx, Matrix.mul_assoc,
        Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h1 (σ i)) j
    rw [pm_eq_mono, mono_mul, mono_mul] at h2
    simp only [Equiv.symm_apply_apply, Units.val_one, one_mul] at h2
    have h3 : j < m.1.symm (σ i) := by
      have := (hb i).not.2 (not_lt.2 hi)
      rw [Fin.lt_def]; omega
    rw [h2, unip_lower hu' h3, mul_zero]
  have hu1 := (isUniUp_iff u).2 hu
  have hx1 : x = u * pm g σ * ((pm g σ)⁻¹ * u⁻¹ * x) := by group
  refine ⟨σ, ⟨hσ, u, _, hu1, hp, hx1⟩, ?_⟩
  rintro τ ⟨hτ, v, q, hv, hq, hx2⟩
  have h1 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ σ) := key_mono (fun _ => Iff.rfl) hσ
  have h2 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ τ) := key_mono (fun r =>
    ⟨block_of_eq hu1 hv hp hq (hx1.symm.trans hx2) r, block_of_eq hv hu1 hq hp (hx2.symm.trans hx1) r⟩) hτ
  exact Equiv.ext fun i => key_injective _ (congrFun (Tuple.unique_monotone h2 h1) i)

end GlobalTheory.GLm.Shuffle
end

section

noncomputable section

namespace GlobalTheory.GLm.Recip

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem toG_coe {g : ℕ} [Fact g.Prime] {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  unfold toG
  rw [dite_eq_left h.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem coe_toG {g : ℕ} [Fact g.Prime] {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG
  rw [dite_eq_left h]
  exact IsUnit.unit_spec _

theorem mean_conj {G : Type} [Group G] [Fintype G] (χ F : G → ℂ) (hχ : IsClass χ) (c : ℂ) :
    mean (fun x => χ x * (c * ∑ y, F (y⁻¹ * x * y))) = c * ∑ x, F x * χ x := by
  unfold mean
  have h1 : ∀ y : G, ∑ x, χ x * F (y⁻¹ * x * y) = ∑ x, F x * χ x := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ ?_
    intro x
    have : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [hχ, this, mul_comm]
  have h2 : ∑ x, χ x * (c * ∑ y, F (y⁻¹ * x * y)) = c * ∑ y : G, ∑ x, χ x * F (y⁻¹ * x * y) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]; ring
  have h3 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h2]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mean_res (g : ℕ) [Fact g.Prime] (c d n : ℕ) (hn : n = c + d) (χ : Gn g n → ℂ)
    (Λ : Gn g c → Gn g d → ℂ) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) =
      ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n,
        if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
  obtain ⟨-, -, hu, -, -, hcard⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g c d n hn
  have key : ∀ x : Gn g n, (∑ p : Gn g c × Gn g d, Λ p.1 p.2 *
      (if InPar c (x : Mt g n) ∧ tl c (x : Mt g n) = (p.1 : Mt g c) ∧ br c d (x : Mt g n) = (p.2 : Mt g d)
        then χ x else 0)) =
      if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
    intro x
    by_cases hx : InPar c (x : Mt g n)
    · obtain ⟨h1, h2⟩ := hu x hx
      rw [if_pos hx, Finset.sum_eq_single (toG (tl c (x : Mt g n)), toG (br c d (x : Mt g n)))]
      · rw [if_pos ⟨hx, (coe_toG h1).symm, (coe_toG h2).symm⟩]
      · intro p _ hp
        rw [if_neg, mul_zero]
        rintro ⟨-, e1, e2⟩
        apply hp
        rw [e1, e2, toG_coe, toG_coe]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hx]
  unfold mean res
  rw [hcard]
  simp only [← key]
  rw [Finset.sum_comm (γ := Gn g n), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, Fintype.card_prod]
  push_cast
  rw [mul_inv (_ * _)]
  ring

theorem eq_of_mean (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ)
    (hA1 : ∀ y, IsClass fun x => A x y) (hA2 : ∀ x, IsClass (A x)) (hB1 : ∀ y, IsClass fun x => B x y)
    (hB2 : ∀ x, IsClass (B x))
    (h : ∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) →
      mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) :
    A = B := by
  have h0 := h (fun x y => (starRingEnd ℂ) (A x y - B x y))
    (fun y x z => by
      have e1 := hA1 y x z
      have e2 := hB1 y x z
      simp only at e1 e2 ⊢
      rw [e1, e2])
    (fun x y z => by
      simp only
      rw [hA2 x y z, hB2 x y z])
  unfold mean at h0
  have h3 : (Fintype.card (G₁ × G₂) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have h1 := sub_eq_zero.mpr (mul_left_cancel₀ h3 h0)
  rw [← Finset.sum_sub_distrib] at h1
  have h2 : ∑ p : G₁ × G₂, Complex.normSq (A p.1 p.2 - B p.1 p.2) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h2
  funext x y
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (h2 (x, y) (Finset.mem_univ _)))

theorem reciprocity : ∀ (g : ℕ) [Fact g.Prime] , (∀ (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ), IsClass χ → mean (fun x => χ x * hcT a b Φ n x) = mean (fun p : Gn g a × Gn g b => res a b χ p.1 p.2 * Φ p.1 p.2)) ∧ (∀ (c d n : ℕ), n = c + d → ∀ (χ : Gn g n → ℂ) (Λ : Gn g c → Gn g d → ℂ), mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) = ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n, if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0) ∧ ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ), (∀ y, IsClass fun x => A x y) → (∀ x, IsClass (A x)) → (∀ y, IsClass fun x => B x y) → (∀ x, IsClass (B x)) → (∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) → mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) → A = B := by
  intro g _
  refine ⟨?_, mean_res g, eq_of_mean⟩
  intro a b n hn χ Φ hχ
  have h1 := mean_res g a b n hn χ Φ
  have h2 := mean_conj χ (fun x : Gn g n => if InPar a (x : Mt g n) then
    Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) hχ
    ((Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card : ℂ)⁻¹
  simp only [ite_mul, zero_mul] at h2
  rw [← h1] at h2
  simp only [mul_comm (res a b χ _ _)]
  exact h2

end GlobalTheory.GLm.Recip
end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerTail

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.triangle_succ, Nat.triangle_succ, ih]
    ring

variable {g : ℕ} [Fact g.Prime]

theorem entN_tl (m : ℕ) {n : ℕ} (M : Mt g n) {a b : ℕ} (ha : a < m) (hb : b < m) :
    entN (tl m M) a b = entN M a b := by
  rw [entN, dite_eq_left ⟨ha, hb⟩]; rfl

theorem entN_fin {n : ℕ} (M : Mt g n) (a b : Fin n) : entN M a b = M a b := by
  rw [entN, dite_eq_left ⟨a.2, b.2⟩]

theorem inR_iff (i : ℕ) {n : ℕ} (M : Mt g n) :
    InR i M ↔ ∀ a : ℕ, i ≤ a → a < n → (∀ b, b < a → entN M a b = 0) ∧ entN M a a = 1 := by
  constructor
  · rintro ⟨h1, h2⟩ a hia han
    refine ⟨fun b hb => ?_, ?_⟩
    · by_cases hbi : b < i
      · have := h1 ⟨a, han⟩ ⟨b, by omega⟩ hbi hia
        exact (entN_fin M ⟨a, han⟩ ⟨b, by omega⟩).trans this
      · have := (h2 ⟨a - i, by omega⟩ ⟨b - i, by omega⟩).1 (by simp only [Fin.mk_lt_mk]; omega)
        simp only [br] at this
        rwa [show i + (a - i) = a by omega, show i + (b - i) = b by omega] at this
    · have := (h2 ⟨a - i, by omega⟩ ⟨a - i, by omega⟩).2 rfl
      simp only [br] at this
      rwa [show i + (a - i) = a by omega] at this
  · intro h
    refine ⟨fun a b hb ha => ?_, fun a b => ⟨fun hab => ?_, fun hab => ?_⟩⟩
    · exact (entN_fin M a b).symm.trans ((h a ha a.2).1 b (by omega))
    · have := a.2
      have hab' : (b : ℕ) < a := hab
      exact (h (i + a) (by omega) (by omega)).1 (i + b) (by omega)
    · subst hab
      have := a.2
      exact (h (i + a) (by omega) (by omega)).2

theorem inR_split {i m n : ℕ} (him : i ≤ m) (hmn : m ≤ n) (M : Mt g n) :
    InR i M ↔ InR m M ∧ InR i (tl m M) := by
  simp only [inR_iff]
  constructor
  · intro h
    refine ⟨fun a ha han => h a (by omega) han, fun a ha ham => ⟨fun b hb => ?_, ?_⟩⟩
    · rw [entN_tl m M ham (by omega)]
      exact (h a ha (by omega)).1 b hb
    · rw [entN_tl m M ham ham]
      exact (h a ha (by omega)).2
  · rintro ⟨h1, h2⟩ a ha han
    by_cases ham : a < m
    · refine ⟨fun b hb => ?_, ?_⟩
      · rw [← entN_tl m M ham (by omega)]
        exact (h2 a ha ham).1 b hb
      · rw [← entN_tl m M ham ham]
        exact (h2 a ha ham).2
    · exact h1 a (by omega) han

theorem tl_tl {i m n : ℕ} (him : i ≤ m) (M : Mt g n) : tl i (tl m M) = tl i M := by
  funext a b
  have := a.2
  have := b.2
  exact entN_tl m M (by omega) (by omega)

theorem supFrom_split {i m n : ℕ} (him : i < m) (hmn : m ≤ n) (M : Mt g n) :
    supFrom i M = supFrom (m - 1) M + supFrom i (tl m M) := by
  unfold supFrom
  rw [add_comm, ← Finset.sum_Ico_consecutive _ (show i ≤ m - 1 by omega) (show m - 1 ≤ n - 1 by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact (entN_tl m M (by omega) (by omega)).symm

theorem der_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ),
    i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  intro g _ ψ i m n F him hmn
  funext h
  rw [GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i m _ h him.le, GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i n _ h (by omega)]
  have he : i * (n - i) + (n - i) * (n - i - 1) / 2 =
      (i * (m - i) + (m - i) * (m - i - 1) / 2) + (m * (n - m) + (n - m) * (n - m - 1) / 2) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le him.le
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [show i + a + b - i = a + b by omega, show i + a - i = a by omega, show i + a + b - (i + a) = b by omega,
      tri_add]
    ring
  rw [he, pow_add _ _ (m * (n - m) + (n - m) * (n - m - 1) / 2), mul_inv _ ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2)),
    mul_assoc]
  congr 1
  unfold tail
  set c : ℂ := ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹
  have h1 : ∀ p : Gn g m, (if InR i (p : Mt g m) ∧ tl i (p : Mt g m) = (h : Mt g i) then
      (c * ∑ x : Gn g n, if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
        F x * (ψ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0) * (ψ (supFrom i (p : Mt g m)))⁻¹ else 0) =
      c * ∑ x : Gn g n, if tl m (x : Mt g n) = (p : Mt g m) then
        (if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
          F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0) else 0 := by
    intro p
    split_ifs with hp
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx]
        rw [← hx] at hp
        rw [tl_tl him.le] at hp
        rw [inR_split him.le hmn (x : Mt g n), supFrom_split him hmn (x : Mt g n), AddChar.map_add_eq_mul, mul_inv,
          ← hx]
        by_cases hR : InR m (x : Mt g n)
        · rw [if_pos ⟨hR, rfl⟩, if_pos ⟨⟨hR, hp.1⟩, hp.2⟩, mul_assoc]
        · rw [if_neg (fun hh => hR hh.1), if_neg (fun hh => hR hh.1.1), zero_mul]
      · rw [if_neg hx, if_neg (fun hh => hx hh.2), zero_mul]
    · symm
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx, if_neg]
        rintro ⟨ha, hb⟩
        apply hp
        rw [← hx, tl_tl him.le]
        exact ⟨((inR_split him.le hmn _).1 ha).2, hb⟩
      · rw [if_neg hx]
  rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i)
  · have hu : IsUnit (tl m (x : Mt g n)) :=
      ((GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g m (n - m) n (by omega)).2.2.1 x ((inR_split him.le hmn _).1 hx.1).1.1).1
    obtain ⟨p, hp⟩ := hu
    rw [Finset.sum_eq_single p]
    · rw [if_pos hp.symm]
    · intro q _ hq
      rw [if_neg]
      intro hh
      exact hq (Units.ext (hp.trans hh).symm)
    · intro hh
      exact absurd (Finset.mem_univ p) hh
  · simp [hx]

end GlobalTheory.GLm.DerTail
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_sigmaFinite_unique : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ ∀ μ', IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ' → μ' = μ := by
  first | exact @GlobalTheory.GaugeSubHaar.isGaugeSub_haar | exact GlobalTheory.GaugeSubHaar.isGaugeSub_haar | (intros; apply GlobalTheory.GaugeSubHaar.isGaugeSub_haar <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ flagM ε W = {g | uMat g - 1 ∈ A} := by
  first | exact @GlobalTheory.LeviAlgebra.exists_levi_algebra | exact GlobalTheory.LeviAlgebra.exists_levi_algebra | (intros; apply GlobalTheory.LeviAlgebra.exists_levi_algebra <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselTorusElement_properties : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 → aT k r α ∈ B.GV k r ∧ (∀ z, inWb k r z → (∀ h ∈ UWset k r z, aT k r α * h = h * aT k r α) ∧ ∀ n ∈ Nset k r, aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r ∧ (aT k r α)⁻¹ * n * aT k r α ∈ Nset k r ∧ ell k r z (aT k r α * n * (aT k r α)⁻¹) = α * ell k r z n) ∧ (∀ z z', inWb k r z → inWb k r z' → ∀ (g : B.Mat k r) (a b : Fin (r + 1)), Zhat k r z z' ((aT k r α)⁻¹ * g * aT k r α) a b = (star α) ^ (r - a.val) * α ^ (r - b.val) * Zhat k r z z' g a b) ∧ ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (aT k r α)⁻¹ * bigCell k r c μ * aT k r α = bigCell k r (fun a => ((‖α‖ ^ (2 * (r - a.val)) : ℝ) : ℂ) * c a) μ := by
  first | exact @GlobalTheory.ThA.TorusElt.torusElt | exact GlobalTheory.ThA.TorusElt.torusElt | (intros; apply GlobalTheory.ThA.TorusElt.torusElt <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitudeOperatorNorm_finalArithmetic_le : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  first | exact @GlobalTheory.Amp.absArith | exact GlobalTheory.Amp.absArith | (intros; apply GlobalTheory.Amp.absArith <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.mass_ratio_rank_factor : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M → Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E = rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | exact GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | (intros; apply GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  first | exact @GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | exact GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | (intros; apply GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag <;> assumption)
end
