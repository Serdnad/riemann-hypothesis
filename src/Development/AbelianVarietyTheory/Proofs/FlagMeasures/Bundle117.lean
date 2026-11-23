module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.GLm.DerClass

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

def blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g)) (D : Mt g b) :
    Mt g (a + b) :=
  (Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem exists_blocks (M : Mt g (a + b)) : ∃ A B C D, M = blocks A B C D := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blocks, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
theorem _root_.GlobalTheory.GLm.DerClass.blocks_mul (A A' : _root_.GlobalTheory.GLq.Mt g a)
    (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (C C' : Matrix (Fin b) (Fin a) (ZMod g))
    (D D' : _root_.GlobalTheory.GLq.Mt g b) :
    _root_.GlobalTheory.GLm.DerClass.blocks A B C D * _root_.GlobalTheory.GLm.DerClass.blocks A' B' C' D' =
      _root_.GlobalTheory.GLm.DerClass.blocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C')
        (C * B' + D * D') := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
theorem _root_.GlobalTheory.GLm.DerClass.blocks_one :
    _root_.GlobalTheory.GLm.DerClass.blocks (1 : _root_.GlobalTheory.GLq.Mt g a) 0 0 (1 : _root_.GlobalTheory.GLq.Mt g b) = 1 := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem tl_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : tl a (blocks A B C D) = A := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [tl, entN, dite_eq_left ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.castAdd b i) (Fin.castAdd b j) = _
  simp [blocks]

theorem br_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : br a b (blocks A B C D) = D := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [br, entN, dite_eq_left ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.natAdd a i) (Fin.natAdd a j) = _
  simp [blocks]

theorem inPar_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : InPar a (blocks A B C D) ↔ C = 0 := by
  constructor
  · intro h
    ext i j
    have := h (Fin.natAdd a i) (Fin.castAdd b j) (by simp) (by simp)
    simpa [blocks] using this
  · rintro rfl i j hj hi
    induction i using Fin.addCases with
    | left i => have := i.2; simp at hi; omega
    | right i =>
      induction j using Fin.addCases with
      | left j => simp [blocks]
      | right j => simp at hj

theorem inMir_blocks (hb : 0 < b) (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) {D : Mt g b} (hD : IsUniUp D) :
    InMir (blocks A B 0 D) := by
  intro i j hi
  rw [← blocks_one]
  induction i using Fin.addCases with
  | left i => have := i.2; simp at hi; omega
  | right i =>
    induction j using Fin.addCases with
    | left j => simp [blocks]
    | right j =>
      have hj := j.2
      simp only [Fin.val_natAdd] at hi
      simp only [blocks, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
      by_cases h : i = j
      · rw [(hD i j).2 h, h, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne h]
        refine (hD i j).1 ?_
        have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
        rw [Fin.lt_def]
        omega

theorem isUniUp_one : IsUniUp (1 : Mt g b) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by rw [h, Matrix.one_apply_eq]⟩

def dg (b : ℕ) (y : Gn g a) : Gn g (a + b) where
  val := blocks y.val 0 0 1
  inv := blocks (y⁻¹).val 0 0 1
  val_inv := by rw [blocks_mul]; simpa using blocks_one
  inv_val := by rw [blocks_mul]; simpa using blocks_one

theorem conj_val (y : Gn g a) (x : Gn g (a + b)) {A : Mt g a} {B : Matrix (Fin a) (Fin b) (ZMod g)}
    {C : Matrix (Fin b) (Fin a) (ZMod g)} {D : Mt g b} (hx : x.val = blocks A B C D) :
    (dg b y * x * (dg b y)⁻¹).val = blocks (y.val * A * (y⁻¹).val) (y.val * B) (C * (y⁻¹).val) D := by
  change blocks y.val 0 0 1 * x.val * blocks (y⁻¹).val 0 0 1 = _
  rw [hx, blocks_mul, blocks_mul]
  simp

theorem res_conj (hb : 0 < b) {F : Gn g (a + b) → ℂ} (hF : IsMirClass F) (h y : Gn g a) (u : Gn g b)
    (hu : IsUniUp (u : Mt g b)) : res a b F (y * h * y⁻¹) u = res a b F h u := by
  unfold res
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dg b y)).toEquiv _ _ fun x => ?_
  obtain ⟨A, B, C, D, hx⟩ := exists_blocks x.val
  have e := conj_val y x hx
  change _ = if InPar a (dg b y * x * (dg b y)⁻¹).val ∧ tl a (dg b y * x * (dg b y)⁻¹).val = (y * h * y⁻¹).val ∧
    br a b (dg b y * x * (dg b y)⁻¹).val = u.val then F (dg b y * x * (dg b y)⁻¹) else 0
  rw [e, hx, inPar_blocks, inPar_blocks, tl_blocks, tl_blocks, br_blocks, br_blocks]
  have h1 : C * (y⁻¹).val = 0 ↔ C = 0 := by
    constructor
    · intro hc
      have := congrArg (· * y.val) hc
      simpa [Matrix.mul_assoc] using this
    · rintro rfl
      simp
  have h2 : y.val * A * (y⁻¹).val = (y * h * y⁻¹).val ↔ A = h.val := by
    rw [Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
  simp only [h1, h2]
  split_ifs with hc
  · obtain ⟨rfl, -, rfl⟩ := hc
    refine (hF _ _ ?_ ?_).symm
    · exact inMir_blocks hb _ _ isUniUp_one
    · rw [hx]
      exact inMir_blocks hb _ _ hu
  · rfl

theorem wh_congr (ψ : AddChar (ZMod g) ℂ) {α β : Gn g b → ℂ} (h : ∀ u : Gn g b, IsUniUp (u : Mt g b) → α u = β u) :
    wh ψ α = wh ψ β := by
  unfold wh tr
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : IsUniUp (u : Mt g b)
  · rw [h u hu]
  · have : (eU g b ψ).coeff u = 0 := by
      simp only [eU, eDat, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
        Finsupp.smul_apply, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_zero, smul_zero]
      intro v hv
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hu (Finset.mem_filter.1 hv).2
    rw [this, zero_mul, zero_mul]

theorem isClass_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n →
    IsMirClass F → IsClass (der ψ i F) := by
  intro g _ ψ i n F hin hF h y
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hin.le
  unfold der
  rw [Nat.add_sub_cancel_left]
  exact wh_congr ψ fun u hu => res_conj (by omega) hF h y u hu

end GlobalTheory.GLm.DerClass
end
end

section

noncomputable section

namespace GlobalTheory.GLm.TailClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {m k : ℕ}

def dM (k : ℕ) (A : Mt g m) : Mt g (m + k) :=
  (Matrix.fromBlocks A 0 0 (1 : Mt g k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem dM_mul (A B : Mt g m) : dM k A * dM k B = dM k (A * B) := by
  simp [dM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem dM_one : dM k (1 : Mt g m) = 1 := by
  simp [dM, Matrix.fromBlocks_one]

def dG (k : ℕ) (p : Gn g m) : Gn g (m + k) :=
  ⟨dM k p.val, dM k p.inv, by rw [dM_mul, p.val_inv, dM_one], by rw [dM_mul, p.inv_val, dM_one]⟩

theorem conj_val (p : Gn g m) (x : Gn g (m + k)) :
    ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) =
      dM k (p : Mt g m) * (x : Mt g (m + k)) * dM k ((p⁻¹ : Gn g m) : Mt g m) := rfl

theorem tl_apply (X : Mt g (m + k)) (i j : Fin m) : tl m X i j = X (Fin.castAdd k i) (Fin.castAdd k j) := by
  have h : (i : ℕ) < m + k ∧ (j : ℕ) < m + k := ⟨by omega, by omega⟩
  rw [tl, entN, dif_pos h]; rfl

theorem upperLeftBlock_blockDiagExtendByIdentity_conj (A B : Mt g m) (X : Mt g (m + k)) : tl m (dM k A * X * dM k B) = A * tl m X * B := by
  ext i j
  simp [tl_apply, dM, Matrix.mul_apply, Fin.sum_univ_add]

theorem blockDiagExtendByIdentity_conj_upperRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin m) (j : Fin k) :
    (dM k A * X * dM k B) (Fin.castAdd k i) (Fin.natAdd m j) =
      ∑ l, A i l * X (Fin.castAdd k l) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerLeft_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin k) (j : Fin m) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.castAdd k j) =
      ∑ l, X (Fin.natAdd m i) (Fin.castAdd k l) * B l j := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i j : Fin k) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.natAdd m j) = X (Fin.natAdd m i) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem entN_blockDiagExtendByIdentity_conj_lowerRight (A B : Mt g m) (X : Mt g (m + k)) (i j : ℕ) (hi : m ≤ i) (hj : m ≤ j) :
    entN (dM k A * X * dM k B) i j = entN X i j := by
  unfold entN
  split_ifs with h
  · have e1 : (⟨i, h.1⟩ : Fin (m + k)) = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : (⟨j, h.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨j - m, by omega⟩ := by ext; simp; omega
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerRight_apply]
  · rfl

theorem inR_conj (A B : Mt g m) (X : Mt g (m + k)) (h : InR m X) : InR m (dM k A * X * dM k B) := by
  refine ⟨fun i j hj hi => ?_, ?_⟩
  · have e1 : i = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerLeft_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [h.1 _ _ (by simp) (by simp), zero_mul]
  · have : br m (m + k - m) (dM k A * X * dM k B) = br m (m + k - m) X := by
      ext i j
      exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ (by omega) (by omega)
    rw [this]; exact h.2

theorem supFrom_conj (hm : 1 ≤ m) (A B : Mt g m) (hA : InMir A) (X : Mt g (m + k)) :
    supFrom (m - 1) (dM k A * X * dM k B) = supFrom (m - 1) X := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  by_cases h : m ≤ j
  · exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ h (by omega)
  · have h' : j < m + k ∧ j + 1 < m + k := ⟨by omega, by omega⟩
    have e1 : (⟨j, h'.1⟩ : Fin (m + k)) = Fin.castAdd k ⟨j, by omega⟩ := by ext; simp
    have e2 : (⟨j + 1, h'.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨0, by omega⟩ := by ext; simp; omega
    rw [entN, entN, dif_pos h', dif_pos h', e1, e2, blockDiagExtendByIdentity_conj_upperRight_apply]
    have : ∀ l, A ⟨j, by omega⟩ l = (1 : Mt g m) ⟨j, by omega⟩ l := fun l => hA _ _ (by simp; omega)
    simp [this, Matrix.one_apply]

theorem inMir_of (X : Mt g (m + k)) (h : InR m X) (h0 : InMir (tl m X)) : InMir X := by
  intro i j hi
  by_cases him : (i : ℕ) < m
  · have hj : (j : ℕ) < m := by omega
    have e1 : i = Fin.castAdd k ⟨i, him⟩ := by ext; simp
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    have := h0 ⟨i, him⟩ ⟨j, hj⟩ (by simp; omega)
    rw [tl_apply, ← e1, ← e2] at this
    rw [this]
    simp [Matrix.one_apply, Fin.ext_iff]
  · by_cases hj : (j : ℕ) < m
    · rw [h.1 i j hj (by omega), Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h2 := h.2 ⟨i - m, by omega⟩ ⟨j - m, by omega⟩
      have h' : m + (i - m) < m + k ∧ m + (j - m) < m + k := ⟨by omega, by omega⟩
      have e1 : (⟨m + (i - m), h'.1⟩ : Fin (m + k)) = i := by ext; simp; omega
      have e2 : (⟨m + (j - m), h'.2⟩ : Fin (m + k)) = j := by ext; simp; omega
      simp only [br, entN, dif_pos h', e1, e2] at h2
      by_cases e : i = j
      · subst e
        rw [h2.2 rfl, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne e]
        refine h2.1 ?_
        have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
        rw [Fin.lt_def]
        simp only
        omega

theorem inMir_dM (A : Mt g m) (hA : InMir A) : InMir (dM k A) := by
  have e : dM k A = dM k A * 1 * dM k 1 := by rw [dM_one, mul_one, mul_one]
  have h1 : InR m (1 : Mt g (m + k)) := by
    refine ⟨fun i j hj hi => Matrix.one_apply_ne (by intro e; subst e; omega), fun a b => ?_⟩
    have h' : m + a < m + k ∧ m + b < m + k := ⟨by omega, by omega⟩
    simp only [br, entN, dif_pos h', Matrix.one_apply, Fin.ext_iff, Fin.lt_def]
    constructor
    · intro h; rw [if_neg (by omega)]
    · intro h; rw [if_pos (by omega)]
  have h2 : tl m (1 : Mt g (m + k)) = 1 := by
    ext i j
    simp [tl_apply, Matrix.one_apply, Fin.ext_iff]
  refine inMir_of _ (e ▸ inR_conj _ _ _ h1) ?_
  rw [e, upperLeftBlock_blockDiagExtendByIdentity_conj, h2, mul_one, mul_one]
  exact hA

theorem isMirClass_tail (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hF : IsMirClass F) : IsMirClass (tail ψ m F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro p x₀ hp hx₀
  unfold tail
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dG k p)).toEquiv _ _ fun x => ?_
  have e : (MulAut.conj (dG k p)).toEquiv x = dG k p * x * (dG k p)⁻¹ := rfl
  rw [e]
  have hiff : (InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)) ↔
      (InR m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) ∧
        tl m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) = ((p * x₀ * p⁻¹ : Gn g m) : Mt g m)) := by
    rw [conj_val, upperLeftBlock_blockDiagExtendByIdentity_conj, Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
    refine and_congr_left fun _ => ⟨inR_conj _ _ _, fun h => ?_⟩
    have := inR_conj ((p⁻¹ : Gn g m) : Mt g m) (p : Mt g m) _ h
    rwa [← mul_assoc, ← mul_assoc, mul_assoc _ (dM k _) (dM k _), dM_mul, Units.inv_mul, dM_one,
      one_mul, mul_one] at this
  by_cases h : InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)
  · rw [if_pos h, if_pos (hiff.1 h), hF _ _ (inMir_dM _ hp) (inMir_of _ h.1 (h.2 ▸ hx₀)), conj_val,
      supFrom_conj hm _ _ hp]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

end GlobalTheory.GLm.TailClass
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusComp

def ht {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * μ i

theorem ht_add {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ + ν) = ht μ + ht ν := by
  simp [ht, mul_add, Finset.sum_add_distrib]

theorem ht_sub {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ - ν) = ht μ - ht ν := by
  simp [ht, mul_sub, Finset.sum_sub_distrib]

theorem ht_root {n : ℕ} (a b : Fin n) : ht (Formalism.REAL.root a b) = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [ht, Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem weight_shift {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {ν : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F ν x) {a b : Fin n} (hab : ε a = ε b) :
    Formalism.REAL.IsWeight F (ν + Formalism.REAL.root a b) (F a b x) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ W => T x) (hF c c a b rfl hab)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, add_smul, add_comm]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, add_smul, sub_smul, add_comm]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2]

theorem word_weight {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {μ : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F μ x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∃ ν, ht μ ≤ ht ν ∧ Formalism.REAL.IsWeight F ν (ew F w x) := by
  induction w with
  | nil => exact ⟨μ, le_rfl, by simpa [ew] using hx⟩
  | cons p w ih =>
    obtain ⟨ν, h1, h2⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p (List.mem_cons_self ..)
    refine ⟨ν + Formalism.REAL.root p.1 p.2, ?_, ?_⟩
    · rw [ht_add, ht_root]
      have : ((p.2 : ℕ) : ℝ) < ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp.2
      linarith
    · simpa only [ew, Module.End.mul_apply] using weight_shift hF h2 hp.1

theorem comp_weight {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℝ} {G : Arr V n 1}
    (hG : Formalism.REAL.IsWeight (arrE E 1) ν G) (a b : Fin n) :
    Formalism.REAL.IsWeight E (ν - Formalism.REAL.root a b) (G (fun _ => (a, b))) := by
  intro c
  have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hG c)
  simp only at h1
  rw [arr_operator_one_apply, PiLp.smul_apply, add_comm, ← eq_sub_iff_add_eq] at h1
  rw [h1]
  by_cases h1 : a = c <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, sub_smul]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, Ne.symm h1, add_smul, sub_smul]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2, Ne.symm h1]

theorem isoPart_stable {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (T : Set (Fin n → ℝ)) (S : Submodule ℂ W) :
    Formalism.REAL.KStable ε F (isoPart ε F T S) := by
  intro a b hab x hx
  have : isoPart ε F T S ≤ (isoPart ε F T S).comap (F a b) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh z hz
    exact compact_span_le_isotypic_part hy hμ hyh (compact_span_stable_general y a b hab z hz)
  exact this hx

theorem vminus_comp : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (abelian₂ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E abelian₂ u → FiniteDimensional ℂ (kSpan ε E u) → KStable ε (arrE E 1) (Vminus ε E abelian₂ u) ∧ Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 ∧ FiniteDimensional ℂ (Vminus ε E abelian₂ u) ∧ ∀ G ∈ Vminus ε E abelian₂ u, ∀ a b, ¬ b < a → ⟪u, at1 G a b⟫_ℂ = 0 := by
  intro V _ _ n ε E abelian₂ u hg hu hΛ hfd
  have hle : Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 := by
    apply isotypic_part_le_of_forall
    intro y hy μ _ _
    exact compact_span_le_of_stable noncompact_arr_one_compact_stable hy
  have hfd0 := noncompact_arr_finite_dimensional (j := 1) hfd
  refine ⟨isoPart_stable _ _, hle, Submodule.finiteDimensional_of_le hle, ?_⟩
  intro G hG a b hab
  have hKR := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  let ℓ : Arr V n 1 →ₗ[ℂ] ℂ := (innerₛₗ ℂ u) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V) (fun _ => (a, b)) ∘ₗ arrOf V n 1)
  have hℓ : ∀ G : Arr V n 1, ℓ G = ⟪u, G (fun _ => (a, b))⟫_ℂ := fun G => rfl
  have hker : Vminus ε E abelian₂ u ≤ LinearMap.ker ℓ := by
    apply isotypic_part_le_of_forall
    rintro y - μ ⟨a', b', hba, -, rfl⟩ hyh
    rw [(kLow _ n ε _ _ y hKR hyh).1, lowSpan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨ν, h1, h2⟩ := word_weight hKR hyh.1 w hw
    rw [SetLike.mem_coe, LinearMap.mem_ker, hℓ]
    refine kWtOrth V n ε E _ _ _ _ (isUnitary_kUnit ε E hu) hΛ.1 (comp_weight h2 a b) ?_
    intro h
    have h3 := congrArg ht h
    rw [ht_sub, ht_root] at h3
    rw [ht_add, ht_root] at h1
    have e1 : ((b' : ℕ) : ℝ) < ((a' : ℕ) : ℝ) := by exact_mod_cast hba
    have e2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast not_lt.mp hab
    linarith
  exact hker hG

end GlobalTheory.Jet.VminusComp
end
end
