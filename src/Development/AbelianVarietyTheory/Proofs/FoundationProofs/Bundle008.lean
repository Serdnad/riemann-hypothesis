module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

section

noncomputable section

open Classical
open scoped BigOperators

namespace GlobalTheory.FinWeil

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

structure IsHeis (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) : Prop where
  sg_sg : ∀ r, σ (σ r) = r
  w_add : w + σ w = 1
  add_left : ∀ x y z, γ (x + y) z = γ x z * γ y z
  add_right : ∀ x y z, γ x (y + z) = γ x y * γ x z
  alt : ∀ x, γ x x = 1
  adj : ∀ r x y, γ (r • x) y = γ x (σ r • y)
  zero : ∀ v, W 0 v = v
  comp : ∀ x y v, W x (W y v) = γ (w • x) y • W (x + y) v

def SelfDual (γ : X → X → ℂ) (A : Submodule R X) : Prop := ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1

def Fixes (W : X → M →ₗ[ℂ] M) (A : Submodule R X) (v : M) : Prop := ∀ a ∈ A, W a v = v

def idx (A B : Submodule R X) : ℕ := A.toAddSubgroup.relIndex B.toAddSubgroup

def sumOp (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  ∑ᶠ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, W ((Quotient.out q : B.toAddSubgroup) : X) v

def normOp (lam : ℕ →* ℂ) (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  (lam (idx A B))⁻¹ • sumOp W A B v

def GoodNorm (σ : R →+* R) (lam : ℕ →* ℂ) : Prop :=
  (∀ n, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
    lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧
    ((∀ r ∈ P, σ r ∈ P) → lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P)

def Adj (A B : Submodule R X) : Prop :=
  ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x}

namespace IsHeis

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W)
include h

theorem skew (x y : X) : γ x y * γ y x = 1 := by
  have h1 := h.alt (x + y)
  rw [h.add_left, h.add_right, h.add_right, h.alt, h.alt] at h1
  simpa using h1

theorem ne_zero (x y : X) : γ x y ≠ 0 := left_ne_zero_of_mul_eq_one (h.skew x y)

theorem zero_left (y : X) : γ 0 y = 1 := by
  have h1 := h.add_left 0 0 y
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero 0 y)).1 h1.symm

theorem zero_right (x : X) : γ x 0 = 1 := by
  have h1 := h.add_right x 0 0
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero x 0)).1 h1.symm

theorem neg_left (x y : X) : γ (-x) y = (γ x y)⁻¹ := by
  have h1 := h.add_left (-x) x y
  rw [neg_add_cancel, h.zero_left] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem neg_right (x y : X) : γ x (-y) = (γ x y)⁻¹ := by
  have h1 := h.add_right x (-y) y
  rw [neg_add_cancel, h.zero_right] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem swap (x y : X) : γ y x = (γ x y)⁻¹ := eq_inv_of_mul_eq_one_right (h.skew x y)

theorem swap_eq_one {x y : X} (hxy : γ x y = 1) : γ y x = 1 := by rw [h.swap, hxy, inv_one]

theorem nsmul_left (n : ℕ) (x y : X) : γ (n • x) y = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_left]
  | succ n ih => rw [succ_nsmul, h.add_left, ih, pow_succ]

theorem nsmul_right (n : ℕ) (x y : X) : γ x (n • y) = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_right]
  | succ n ih => rw [succ_nsmul, h.add_right, ih, pow_succ]

theorem comm (x y : X) (v : M) : W x (W y v) = γ x y • W y (W x v) := by
  have h1 : γ (w • x) y = γ x y * γ (w • y) x := by
    have h2 : γ x y = γ (w • x) y * γ (σ w • x) y := by rw [← h.add_left, ← add_smul, h.w_add, one_smul]
    rw [h2, h.adj (σ w), h.sg_sg, mul_assoc, h.skew, mul_one]
  rw [h.comp, h.comp, smul_smul, h1, add_comm]

theorem iso {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) : γ x y = 1 := (hA x).1 hx y hy

theorem comp_of_mem {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) (v : M) :
    W x (W y v) = W (x + y) v := by
  rw [h.comp, h.iso hA (A.smul_mem w hx) hy, one_smul]

theorem neg_comp (x : X) (v : M) : W (-x) (W x v) = γ (w • -x) x • v := by
  rw [h.comp, neg_add_cancel, h.zero]

end IsHeis

end GlobalTheory.FinWeil
end
end

section

namespace GlobalTheory.StandardAdditiveCharacter

theorem exists_stdAddChar_eq (n : ℕ) [NeZero n] (z : ℂ) (hz : z ^ n = 1) :
    ∃ j : ZMod n, ZMod.stdAddChar j = z := by
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz
  refine ⟨((i : ℤ) : ZMod n), ?_⟩
  rw [ZMod.stdAddChar_coe, ← hi, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bijective_dual_addChar (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun (φ : Module.Dual (ZMod n) A) ↦
      AddChar.compAddMonoidHom ZMod.stdAddChar (LinearMap.toAddMonoidHom φ) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro a
    have h' := congr_arg (fun χ : AddChar A ℂ => χ a) h
    simp only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h'
    exact ZMod.injective_stdAddChar h'
  · intro ψ
    have hroot : ∀ a : A, (ψ a) ^ n = 1 := by
      intro a
      rw [← AddChar.map_nsmul_eq_pow]
      have h0 : n • a = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
      rw [h0, AddChar.map_zero_eq_one]
    choose j hj using fun a => exists_stdAddChar_eq n (ψ a) (hroot a)
    let F : A →+ ZMod n :=
      { toFun := j
        map_zero' := ZMod.injective_stdAddChar (by simp [hj])
        map_add' := fun a b => ZMod.injective_stdAddChar (by simp only [AddChar.map_add_eq_mul, hj]) }
    refine ⟨F.toZModLinearMap n, ?_⟩
    ext a
    simp [F, hj]

end GlobalTheory.StandardAdditiveCharacter
end

section

namespace GlobalTheory

theorem relIndex_map_mulLeft_lattice_of_sq_eq_neg :
    ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), 0 < N → α ^ 2 = -(N : ℂ) →
      (∀ l ∈ L.lattice, α * l ∈ L.lattice) →
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex L.lattice.toAddSubgroup
        = N := by
  intro L α N hN hα hL
  have hα0 : α ≠ 0 := by
    rintro rfl
    have : (N : ℂ) = 0 := by simpa using hα
    exact hN.ne' (by exact_mod_cast this)
  have hinj : Function.Injective (AddMonoidHom.mulLeft α) := mul_right_injective₀ hα0
  set A := L.lattice.toAddSubgroup with hA
  set f := AddMonoidHom.mulLeft α with hf
  have h1 : A.map f ≤ A := by
    rintro _ ⟨l, hl, rfl⟩
    exact hL l hl
  have h2 : (A.map f).map f ≤ A.map f := AddSubgroup.map_mono h1
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h2 h1
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at hmul
  have hr : Module.finrank ℤ L.lattice = 2 := by
    simpa using Module.finrank_eq_card_basis L.latticeBasis
  have hidx : ((A.map f).map f).relIndex A = N ^ 2 := by
    rw [← hr, ← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]
    congr 1
    ext x
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
      refine ⟨⟨-l, L.lattice.neg_mem hl⟩, Subtype.ext ?_⟩
      have hx' : α * (α * l) = (x : ℂ) := hx
      show N • (-l) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-l) * hα
    · rintro ⟨l, hx⟩
      have hx' : N • (l : ℂ) = (x : ℂ) := congrArg Subtype.val hx
      refine ⟨_, ⟨-(l : ℂ), L.lattice.neg_mem l.2, rfl⟩, ?_⟩
      show α * (α * -(l : ℂ)) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-(l : ℂ)) * hα
  rw [hidx, ← sq] at hmul
  exact Nat.pow_left_injective two_ne_zero hmul

end GlobalTheory
end

section

namespace GlobalTheory

theorem log_factorial_pow_mul_factorial_pow_le :
    ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R →
      Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ)
        ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  intro n R₀ R hR hR₀
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hf2 : (0 : ℝ) < (R₀.factorial : ℝ) := by exact_mod_cast R₀.factorial_pos
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have h0 : (0 : ℝ) ≤ (R₀ : ℝ) := Nat.cast_nonneg _
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log hf1
    exact_mod_cast n.factorial_le_pow
  have h2 : Real.log (R₀.factorial : ℝ) ≤ R * Real.log R := by
    have h3 : (R₀.factorial : ℝ) ≤ R ^ R₀ := by
      calc (R₀.factorial : ℝ) ≤ (R₀ : ℝ) ^ R₀ := by exact_mod_cast R₀.factorial_le_pow
        _ ≤ R ^ R₀ := pow_le_pow_left₀ h0 hR₀ _
    calc Real.log (R₀.factorial : ℝ) ≤ Real.log (R ^ R₀) := Real.log_le_log hf2 h3
      _ = R₀ * Real.log R := Real.log_pow _ _
      _ ≤ R * Real.log R := mul_le_mul_of_nonneg_right hR₀ hlR
  have hlf : 0 ≤ Real.log (n.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast n.factorial_pos)
  push_cast
  rw [Real.log_mul (pow_pos hf1 _).ne' (pow_pos hf2 _).ne', Real.log_pow, Real.log_pow,
    Real.log_mul (by linarith) (by linarith)]
  push_cast
  have h4 : (R₀ : ℝ) * Real.log (n.factorial : ℝ) ≤ R * (n * Real.log n) :=
    mul_le_mul hR₀ h1 hlf (by linarith)
  have h5 : (n : ℝ) * Real.log (R₀.factorial : ℝ) ≤ n * (R * Real.log R) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : 0 ≤ R * (n * Real.log n) := by positivity
  have h7 : 0 ≤ (n : ℝ) * (R * Real.log R) := by positivity
  nlinarith [h4, h5, h6, h7]

end GlobalTheory
end

section

namespace GlobalTheory.SummCount

theorem summable_prod_fin_tuple {α : Type} {g : α → ℝ} (hg : Summable g) (h0 : ∀ a, 0 ≤ g a)
    (N : ℕ) : Summable fun x : Fin N → α => ∏ i, g (x i) := by
  induction N with
  | zero => exact .of_finite
  | succ N ih =>
    have h := hg.mul_of_nonneg ih h0 fun x => Finset.prod_nonneg fun i _ => h0 _
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => α).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

theorem pow_mul_inv_rpow_eq {b t : ℝ} (hb : 0 < b) (n m : ℕ) :
    b ^ (n * m) * ((b ^ m)⁻¹) ^ t = (b ^ ((n : ℝ) - t)) ^ m := by
  have hx : 0 < b ^ m := pow_pos hb m
  rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, pow_mul', ← Real.rpow_natCast (b ^ m) n,
    ← Real.rpow_add hx, ← Real.rpow_natCast b m, ← Real.rpow_mul hb.le,
    ← Real.rpow_mul_natCast hb.le]
  congr 1
  ring

theorem summable_rpow_of_fibre_card_le (ι : Type) (n : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (n : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (n * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((n : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finsetProd_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (n * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 n, Finset.prod_mul_distrib]
        ring

end GlobalTheory.SummCount
end

section

open Filter Topology

namespace GlobalTheory

theorem prod_Ico_inv_one_sub_inv_sq (M : ℕ) :
    ∏ n ∈ Finset.Ico 2 (M + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ = 2 * ((M : ℝ) + 1) / ((M : ℝ) + 2) := by
  induction M with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.prod_Ico_succ_top (by omega), ih]
    push_cast
    have h1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h3 : (1 - 1 / ((k:ℝ) + 2) ^ 2) = ((k:ℝ)+1)*((k:ℝ)+3) / ((k:ℝ)+2)^2 := by
      field_simp; ring
    rw [h3]
    field_simp
    ring

theorem one_le_inv_one_sub_inv_sq {n : ℕ} (hn : 2 ≤ n) : 1 ≤ (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 1 / (n:ℝ)^2 := by positivity
  have hlt : 1 / (n:ℝ)^2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact one_le_inv₀ (by linarith) |>.mpr (by linarith)

theorem factor_le (s : ℝ) (hs : 0 ≤ s) {p : ℕ} (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (1:ℝ) ≤ p := by linarith
  have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  rw [Real.rpow_two] at hle
  have hsq : (4:ℝ) ≤ (p:ℝ)^2 := by nlinarith
  have hlt : 1 / (p:ℝ)^2 < 1 := by rw [div_lt_one (by positivity)]; linarith
  apply inv_anti₀
  · linarith
  · have : 1 / (p:ℝ) ^ (2 * (1 + s)) ≤ 1 / (p:ℝ)^2 :=
      one_div_le_one_div_of_le (by positivity) hle
    linarith

theorem prod_primesBelow_zeta_two_add_le_two :
    ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  intro s hs N
  have hsub : N.primesBelow ⊆ Finset.Ico 2 (N + 2) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.2.two_le, by omega⟩
  have hmem : ∀ p ∈ N.primesBelow, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primesBelow hp).two_le
  calc ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹
      ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have := one_le_inv_one_sub_inv_sq (hmem p hp)
          have h2 := factor_le s hs (hmem p hp)

          have hp' : (2:ℝ) ≤ p := by exact_mod_cast hmem p hp
          have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          have hpos : 0 < (p:ℝ) ^ (2 * (1 + s)) := by positivity
          have hlt : 1 / (p:ℝ) ^ (2 * (1 + s)) < 1 := by
            rw [div_lt_one hpos]; rw [Real.rpow_two] at hle; nlinarith
          exact inv_nonneg.mpr (by linarith)
        · intro p hp; exact factor_le s hs (hmem p hp)
    _ ≤ ∏ n ∈ Finset.Ico 2 (N + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.prod_sdiff hsub]
        have h0 : 0 ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ :=
          Finset.prod_nonneg fun p hp => le_trans zero_le_one (one_le_inv_one_sub_inv_sq (hmem p hp))
        have h1 : 1 ≤ ∏ n ∈ Finset.Ico 2 (N + 2) \ N.primesBelow, (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
          apply Finset.one_le_prod₀
          intro n hn
          exact one_le_inv_one_sub_inv_sq (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hn).1).1
        nlinarith
    _ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := prod_Ico_inv_one_sub_inv_sq N
    _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith

end GlobalTheory
end

section

open Complex Filter Topology

namespace GlobalTheory

theorem lseries_shift_twist (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) :
    LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  unfold LSeries
  congr 1
  funext n
  simp only [LSeries.term_def]
  split_ifs with hn
  · rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have key : (n : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      (n : ℂ) ^ (e - 1) * (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hn']
    congr 1
    push_cast [Nat.cast_sub he]
    ring
  have h1 : (n : ℂ) ^ (e - 1) ≠ 0 := pow_ne_zero _ hn'
  have h2 : (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [key]
  field_simp

end GlobalTheory
end
