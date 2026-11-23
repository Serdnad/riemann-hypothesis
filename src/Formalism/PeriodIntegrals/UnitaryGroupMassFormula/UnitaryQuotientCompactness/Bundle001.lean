module

public import Formalism.PeriodIntegrals.Bundle012
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ}

def piI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def epsI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma piI_val (i : Fin (2 * r + k + 1)) :
    (piI k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold piI
  split_ifs <;> rfl

lemma piI_piI (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [piI_val, piI_val]
  split_ifs <;> omega

lemma epsI_piI (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by
  have hi := i.isLt
  unfold epsI
  rw [piI_val]
  split_ifs <;> first | rfl | omega

lemma epsI_mul_self (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by
  unfold epsI
  split_ifs <;> norm_num

lemma star_epsI (i : Fin (2 * r + k + 1)) : star (epsI k r i) = epsI k r i := by
  unfold epsI
  split_ifs <;> simp

lemma Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, epsI, Fin.ext_iff, piI_val]
  split_ifs <;> first | rfl | omega

lemma Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = epsI k r i * X (piI k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply, ite_mul]

lemma mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (piI k r j) * epsI k r j := by
  have hc : ∀ l, (j = piI k r l) ↔ (l = piI k r j) :=
    fun l => ⟨fun h => by rw [h, piI_piI], fun h => by rw [h, piI_piI]⟩
  simp only [Matrix.mul_apply, Hpk_apply, hc, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, epsI_piI]

lemma Hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i) :
    (Hpk k r *ᵥ v) i = epsI k r i * v (piI k r i) := by
  simp [Matrix.mulVec, dotProduct, Hpk_apply, ite_mul]

lemma Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [epsI_mul_self]
  · simp [h, Ne.symm h]

lemma Hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = piI k r i
  · have h' : i = piI k r j := by rw [h, piI_piI]
    rw [if_pos h', if_pos h, star_epsI, h, epsI_piI]
  · have h' : ¬ i = piI k r j := fun h' => h (by rw [h', piI_piI])
    rw [if_neg h', if_neg h, star_zero]

lemma inv_mul_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by
    simp only [Matrix.mul_assoc], hg', Hpk_mul_self]

lemma inv_eq_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (inv_mul_UH hg)

lemma mul_inv_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := by
  rw [inv_eq_UH hg]
  exact mul_eq_one_comm.mp (inv_mul_UH hg)

lemma inv_mul_UH' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := by
  rw [inv_eq_UH hg]
  exact inv_mul_UH hg

lemma one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

lemma mul_mem_UH {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma inv_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : a * a⁻¹ = 1 := mul_inv_UH ha
  have h2 : (a⁻¹)ᴴ * aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = ((a⁻¹)ᴴ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

lemma Hpk_mul_mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X * Hpk k r) i j = epsI k r i * X (piI k r i) (piI k r j) * epsI k r j := by
  rw [mul_Hpk_apply, Hpk_mul_apply]

end PI.QuotSetU.UnitaryGroupMassFormula.SW
end
end

section

open MeasureTheory Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

def ModProps {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (D : Matrix (Fin m) (Fin m) ℂ → ℝ) : Prop :=
  (∀ g ∈ G, 0 < D g) ∧ (∀ a ∈ G, ∀ b ∈ G, D (a * b) = D a * D b) ∧
  (∀ c : Matrix (Fin m) (Fin m) ℂ, IsUnit c → (∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) →
      ∀ g ∈ G, D (c * g * c⁻¹) = D g) ∧
  (∀ V ⊆ G, IsCompact V → ∃ M : ℝ, ∀ v ∈ V, D v ≤ M)

def ModExists : Prop :=
  ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)), IsMatGroup G →
    ∃ D : Matrix (Fin m) (Fin m) ℂ → ℝ, ModProps G D ∧
      ((∀ g ∈ G, D g = 1) → ∀ μ : Measure (MtM m), IsHaarOnM G μ → IsRightInvM G μ)

def UHGroup : Prop := ∀ k r : ℕ, IsMatGroup (UH (Hpk k r))

def SsetSub : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Sset k r z ⊆ UH (Hpk k r)

def SsetGroup : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsMatGroup (Sset k r z)

def TrivG : Prop :=
  ∀ (k r : ℕ) (D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ),
    ModProps (UH (Hpk k r)) D → ∀ g ∈ UH (Hpk k r), D g = 1

def TrivS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ,
      ModProps (Sset k r z) D → ∀ g ∈ Sset k r z, D g = 1

def PolarUH : Prop :=
  ∀ (k r : ℕ), ∀ g ∈ UH (Hpk k r), ∃ u p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    u ∈ UH (Hpk k r) ∧ uᴴ * u = 1 ∧ p ∈ UH (Hpk k r) ∧ pᴴ = p ∧ g = u * p

def KCompact : Prop := ∀ k r : ℕ, IsCompact {u | u ∈ UH (Hpk k r) ∧ uᴴ * u = 1}

def UWCompact : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsCompact (UWset k r z)

def NGroup : Prop :=
  ∀ k r : ℕ, (1 ∈ Nset k r) ∧ (∀ a ∈ Nset k r, ∀ b ∈ Nset k r, a * b ∈ Nset k r) ∧
    ∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r

def NContract : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ n ∈ Nset k r, ∀ ε : ℝ, 0 < ε →
    ∃ c : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, IsUnit c ∧
      (∀ g, c * g * c⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z) ∧ ∀ i j, ‖(c * n * c⁻¹ - 1) i j‖ ≤ ε

end PI.QuotSetU.UnitaryGroupMassFormula

end
end
