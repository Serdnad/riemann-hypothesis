module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007

@[expose] public section

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.OneDoubleCoset

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem isClass_mul_comm {φ : G → ℂ} (hφ : IsClass φ) (x y : G) : φ (x * y) = φ (y * x) := by
  have := hφ (y * x) x
  rw [← this]; congr 1; group

theorem coset_sum_mem (K : Subgroup G) (l : K →* ℂˣ) (φ : G → ℂ) (b : K) :
    ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * b) =
      (l b : ℂ) * ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ a := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.coe_mulRight, map_mul, map_inv, mul_inv_rev, inv_inv, Units.val_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]

theorem coset_sum_eq_zero (K : Subgroup G) (l : K →* ℂˣ) {φ : G → ℂ} (hφ : IsClass φ) (h : G)
    (a₀ a₁ : K) (e : (a₁ : G) = h⁻¹ * a₀ * h) (ne : l a₁ ≠ l a₀) :
    ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * h) = 0 := by
  set F := ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * h) with hF
  have key : F = ((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) * F := by
    conv_lhs => rw [hF, ← Equiv.sum_comp ((Equiv.mulRight a₀).trans (Equiv.mulLeft a₁⁻¹))]
    rw [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : φ (((a₁⁻¹ * (c * a₀) : K) : G) * h) = φ (c * h) := by
      rw [← hφ (c * h) (a₁ : G)⁻¹]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
      congr 2
      rw [e]; group
    simp only [Equiv.trans_apply, Equiv.coe_mulRight, Equiv.coe_mulLeft]
    rw [h1]
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv, Units.val_mul]
    ring
  by_contra hne
  apply ne
  have : ((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) = 1 := by
    have h2 : (((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) - 1) * F = 0 := by rw [sub_mul, ← key]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)
  exact mul_inv_eq_one.1 (Units.val_eq_one.1 this)

theorem sum_indicator (H₁ H₂ : Subgroup G) :
    ∑ b : H₂, (if (b : G) ∈ H₁ then (1 : ℂ) else 0) =
      ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) := by
  rw [Finset.sum_boole]
  congr 1
  refine Finset.card_bij (fun b _ => (b : G)) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨hb, b.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact ⟨⟨g, hg.2⟩, by simpa using hg.1, rfl⟩

theorem double_sum (H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ)
    (hag : ∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b)
    (hM : ∀ h ∈ H₂, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a)
    {φ : G → ℂ} (hφ : IsClass φ) :
    ∑ b : H₂, ∑ a : H₁, (((l₂ b)⁻¹ : ℂˣ) : ℂ) * ((((l₁ a)⁻¹ : ℂˣ) : ℂ) * φ (a * b)) =
      ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) *
        ∑ a : H₁, (((l₁ a)⁻¹ : ℂˣ) : ℂ) * φ a := by
  rw [← sum_indicator, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  split_ifs with hb
  · have := coset_sum_mem H₁ l₁ φ ⟨b, hb⟩
    simp only at this
    rw [this, hag ⟨b, hb⟩ b rfl, ← mul_assoc, Units.inv_mul]
  · obtain ⟨a₀, a₁, e, ne⟩ := hM b b.2 hb
    rw [coset_sum_eq_zero H₁ l₁ hφ b a₀ a₁ e ne]; simp

theorem isotypic_trace_eq : ∀ (G : Type) [Group G] [Fintype G] (H H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ), H₁ ≤ H → H₂ ≤ H → Nat.card H₁ = Nat.card H₂ → (∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b) → (∀ h ∈ H, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a) → (∀ h ∈ H, h ∉ H₂ → ∃ b b' : H₂, (b' : G) = h⁻¹ * b * h ∧ l₂ b' ≠ l₂ b) → ∀ φ : G → ℂ, IsClass φ → (Nat.card H₁ : ℂ)⁻¹ * ∑ a : H₁, ((l₁ a)⁻¹ : ℂˣ) * φ a = (Nat.card H₂ : ℂ)⁻¹ * ∑ b : H₂, ((l₂ b)⁻¹ : ℂˣ) * φ b := by
  intro G _ _ H H₁ H₂ l₁ l₂ h1 h2 hc hag hM1 hM2 φ hφ
  have e1 := double_sum H₁ H₂ l₁ l₂ hag (fun h hh => hM1 h (h2 hh)) hφ
  have e2 := double_sum H₂ H₁ l₂ l₁ (fun b a e => (hag a b e.symm).symm)
    (fun h hh => hM2 h (h1 hh)) hφ
  have hf : (Finset.univ.filter fun g : G => g ∈ H₂ ∧ g ∈ H₁) =
      (Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂) :=
    Finset.filter_congr fun g _ => and_comm
  rw [hf, Finset.sum_comm] at e2
  have hN : ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, by simp⟩
  rw [hc]
  congr 1
  apply mul_left_cancel₀ hN
  rw [← e1, ← e2]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [isClass_mul_comm hφ (a : G) b]; ring

end GlobalTheory.GLm.OneDoubleCoset
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParBasic

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem tl_apply (M : Mt g (a + b)) (i j : Fin a) : tl a M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos]
  rfl

theorem br_apply (M : Mt g (a + b)) (i j : Fin b) : br a b M i j = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos]
  rfl

def blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : Mt g (a + b) :=
  (Matrix.fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def ur (a b : ℕ) (M : Mt g (a + b)) : Matrix (Fin a) (Fin b) (ZMod g) :=
  fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)

theorem tl_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : tl a (blkM A B D) = A := by
  ext i j; simp [tl_apply, blkM]

theorem br_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : br a b (blkM A B D) = D := by
  ext i j; simp [br_apply, blkM]

theorem ur_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : ur a b (blkM A B D) = B := by
  ext i j; simp [ur, blkM]

theorem inPar_iff (M : Mt g (a + b)) :
    InPar a M ↔ ∀ (i : Fin b) (j : Fin a), M (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  constructor
  · intro h i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    have := h ⟨i - a, by omega⟩ ⟨j, hj⟩
    convert this using 2 <;> ext <;> simp
    omega

theorem inPar_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : InPar a (blkM A B D) := by
  rw [inPar_iff]
  intro i j; simp [blkM]

theorem blkM_eq {M : Mt g (a + b)} (h : InPar a M) : blkM (tl a M) (ur a b M) (br a b M) = M := by
  rw [inPar_iff] at h
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [blkM, tl_apply, br_apply, ur, h]

theorem det_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    (blkM A B D).det = A.det * D.det := by
  rw [blkM, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem isUnit_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    IsUnit (blkM A B D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [Matrix.isUnit_iff_isUnit_det, det_blkM, IsUnit.mul_iff]

theorem blkM_mul (A A' : Mt g a) (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (D D' : Mt g b) :
    blkM A B D * blkM A' B' D' = blkM (A * A') (A * B' + B * D') (D * D') := by
  rw [blkM, blkM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [blkM]

theorem isUnit_blocks (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    IsUnit (tl a (x : Mt g (a + b))) ∧ IsUnit (br a b (x : Mt g (a + b))) := by
  rw [← isUnit_blkM _ (ur a b x.val), blkM_eq h]
  exact x.isUnit

theorem blocks_mul (x y : Mt g (a + b)) (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) ∧ tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y := by
  have e := blkM_mul (tl a x) (tl a y) (ur a b x) (ur a b y) (br a b x) (br a b y)
  rw [blkM_eq hx, blkM_eq hy] at e
  rw [e]
  exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩

theorem exists_subgroup {G : Type} [Group G] [Finite G] (p : G → Prop) (h1 : p 1)
    (hm : ∀ x y, p x → p y → p (x * y)) : ∃ P : Subgroup G, ∀ x, x ∈ P ↔ p x := by
  have hp : ∀ x, p x → ∀ k : ℕ, p (x ^ k) := fun x hx k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hm _ _ ih hx
  refine ⟨{ carrier := {x | p x}, mul_mem' := fun {x y} => hm x y, one_mem' := h1, inv_mem' := fun {x} hx => ?_ },
    fun x => Iff.rfl⟩
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    have h0 := orderOf_pos x
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
  change p x⁻¹
  rw [this]
  exact hp x hx _

theorem inPar_one (a n : ℕ) : InPar a (1 : Mt g n) := fun i j hj hi =>
  Matrix.one_apply_ne (by rintro rfl; omega)

theorem card_fibre (h₁ : Gn g a) (h₂ : Gn g b) :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b)) ∧
      tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)).card = g ^ (a * b) := by
  have hc : (Finset.univ : Finset (Matrix (Fin a) (Fin b) (ZMod g))).card = g ^ (a * b) := by
    rw [Finset.card_univ]
    change Fintype.card (Fin a → Fin b → ZMod g) = _
    simp [pow_mul']
  rw [← hc]
  refine Finset.card_bij (fun x _ => ur a b x.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro x hx y hy h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply Units.ext
    rw [← blkM_eq hx.1, ← blkM_eq hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2, h]
  · intro B _
    have hu := (isUnit_blkM h₁.val B h₂.val).2 ⟨h₁.isUnit, h₂.isUnit⟩
    refine ⟨hu.unit, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsUnit.unit_spec]
      exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩
    · simp only [IsUnit.unit_spec, ur_blkM]

theorem toG_val {n : ℕ} {M : Mt g n} (h : IsUnit M) : (toG M).val = M := by
  rw [toG, dif_pos h, IsUnit.unit_spec]

theorem card_par :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b))).card =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset (Gn g a × Gn g b)))
    (f := fun x : Gn g (a + b) => (toG (tl a x.val), toG (br a b x.val))) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (g := fun _ => g ^ (a * b))]
  · simp
  · rintro ⟨h₁, h₂⟩ _
    rw [← card_fibre h₁ h₂, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun x _ => and_congr_right fun hx => ?_
    have hu := isUnit_blocks x hx
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]

theorem isUniUp_one (n : ℕ) : IsUniUp (1 : Mt g n) := fun _ _ =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

theorem isUniUp_mul {n : ℕ} (x y : Mt g n) (hx : IsUniUp x) (hy : IsUniUp y) : IsUniUp (x * y) := by
  intro i j
  refine ⟨fun h => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hx i k).1 hk, zero_mul]
    · rw [(hy k j).1 (h.trans_le (not_lt.1 hk)), mul_zero]
  · rintro rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single i, (hx i i).2 rfl, (hy i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hx i k).1 h, zero_mul]
      · rw [(hy k i).1 h, mul_zero]
    · simp

theorem par_basic : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  intro g _ a b n hn
  subst hn
  exact ⟨exists_subgroup _ (inPar_one _ _) fun x y hx hy => (blocks_mul _ _ hx hy).1,
    exists_subgroup _ (isUniUp_one _) fun x y hx hy => isUniUp_mul _ _ hx hy,
    isUnit_blocks, fun x y hx hy => (blocks_mul x y hx hy).2, card_fibre, card_par⟩

end GlobalTheory.GLm.ParBasic
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem trace_mem_adjoin_of_pow_eq_one (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (N : ℕ) (hN : 0 < N) (hf : f ^ N = 1) :
    LinearMap.trace ℂ V f ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine multiset_sum_mem _ ?_
  intro μ hμ
  have hroot : f.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector
  have h1 := hv.pow_apply N
  rw [hf] at h1
  have h2 : μ ^ N = 1 := by
    have h3 : (μ ^ N - 1) • v = 0 := by
      rw [sub_smul, ← h1]; simp
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp N hN.ne').eq_pow_of_pow_eq_one h2
  rw [← hi]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

theorem isChar_mem_adjoin_exp :
    ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ →
      ∀ x, χ x ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  intro G _ _ χ N hN hd hχ x
  obtain ⟨V, hV⟩ := hχ
  rw [← hV x]
  refine trace_mem_adjoin_of_pow_eq_one V (V.ρ x) N hN ?_
  obtain ⟨k, rfl⟩ := hd
  rw [← map_pow, pow_mul, pow_card_eq_one', one_pow, map_one]

end GlobalTheory.GLm
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem exists_irreducible_charpoly_mem_rootsBar (g : ℕ) [Fact g.Prime] (d : ℕ)
    (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ≠ 0) (hd : (minpoly (ZMod g) z).natDegree = d) :
    ∃ y : Gn g d, Irreducible (y : Mt g d).charpoly ∧
      z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly := by
  subst hd
  have hi : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  let pb := IntermediateField.adjoin.powerBasis hi
  let M : Mt g (minpoly (ZMod g) z).natDegree := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = minpoly (ZMod g) z := by
    have h := charpoly_leftMulMatrix pb
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h
    exact h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (minpoly.coeff_zero_ne_zero hi hz)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · change Irreducible M.charpoly
    rw [hM]
    exact minpoly.irreducible hi
  · change z ∈ Formalism.CyclotomicNorms.rootsBar M.charpoly
    rw [hM, Formalism.CyclotomicNorms.rootsBar, mem_roots_map (minpoly.ne_zero hi), ← aeval_def]
    exact minpoly.aeval _ _

end GlobalTheory.GLm
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.GGDeg

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {n : ℕ} {M : Mt g n} (h : IsUniUp M) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular (fun a b hab => (h a b).1 hab),
    Finset.prod_eq_one fun a _ => (h a a).2 rfl]
  exact isUnit_one

theorem card_uniUp_mat (n : ℕ) :
    (Finset.univ.filter fun M : Mt g n => IsUniUp M).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  have h : (Finset.univ.filter fun M : Mt g n => IsUniUp M) =
      (Fintype.piFinset fun a : Fin n => Fintype.piFinset fun b : Fin n =>
        (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)) :
          Finset (Fin n → Fin n → ZMod g)) := by
    ext M
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
    refine Iff.trans ?_ Fintype.mem_piFinset.symm
    refine forall_congr' fun a => Iff.trans (forall_congr' fun b => ?_) Fintype.mem_piFinset.symm
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne, hab.not_gt]
    · subst hab; simp
    · simp [hab, hab.ne', hab.not_gt]
  rw [h]
  erw [Fintype.card_piFinset]
  simp only [Fintype.card_piFinset]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  have h2 : ∀ a : Fin n, (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)).card =
      if a < b then g else 1 := by
    intro a
    split_ifs <;> simp [ZMod.card]
  simp only [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [show (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b by ext; simp]
  simp

theorem card_uniUp (n : ℕ) :
    (Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  rw [← card_uniUp_mat]
  refine Finset.card_bij (fun u _ => (u : Mt g n)) ?_ ?_ ?_
  · intro u hu
    simpa using hu
  · intro u _ v _ h
    exact Units.ext h
  · intro M hM
    have hM' : IsUniUp M := by simpa using hM
    exact ⟨(isUnit_of_isUniUp hM').unit, by simpa using hM', rfl⟩

theorem card_Gn (n : ℕ) : (Fintype.card (Gn g n) : ℂ) =
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) * ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) := by
  have hg : 0 < g := (Fact.out : g.Prime).pos
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have h1 : ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) = ∏ i : Fin n, ((g : ℂ) ^ (n - i) - 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((g : ℂ) ^ (n - i) - 1)) n]
    refine Finset.prod_bij' (fun i _ => n - i) (fun i _ => n - i) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [Finset.mem_Icc, Finset.mem_range] <;> intro i hi
    · omega
    · omega
    · omega
    · omega
    · rw [show n - (n - i) = i by omega]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hg i.2.le), mul_sub, ← pow_add,
    show (i : ℕ) + (n - i) = n by have := i.2; omega]
  push_cast
  ring

theorem gg_one_and_isClass : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ),
    gg ψ n 1 = ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) ∧ IsClass (gg ψ n) := by
  intro g _ ψ n
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  constructor
  · have h1 : IsUniUp (1 : Mt g n) := fun a b =>
      ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq a⟩
    have h2 : ∀ i, entN (1 : Mt g n) i (i + 1) = 0 := by
      intro i
      unfold entN
      split_ifs with h
      · exact Matrix.one_apply_ne (by simp)
      · rfl
    unfold gg
    simp only [mul_one, inv_mul_cancel, Units.val_one, h1, if_true, h2, Finset.sum_const_zero,
      AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [card_uniUp, card_Gn]
    push_cast
    rw [inv_mul_cancel_left₀ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hg)]
  · intro x z
    unfold gg
    congr 1
    refine (Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun y => ?_).symm
    have : (Equiv.mulLeft z y)⁻¹ * (z * x * z⁻¹) * (Equiv.mulLeft z y) = y⁻¹ * x * y := by
      simp [mul_assoc]
    rw [this]

end GlobalTheory.GLq.GGDeg
end
