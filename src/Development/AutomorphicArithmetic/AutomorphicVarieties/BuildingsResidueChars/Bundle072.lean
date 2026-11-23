module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle060
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.RibetLat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Connected.Separation

@[expose] public section

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd.S2 GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem um_add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

private theorem um_add_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem um_sub_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact um_add_lt ha (by rwa [norm_neg])

private theorem um_sub_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact um_add_le ha (by rwa [norm_neg])

private theorem le_of_cong {a x : K} (h : ‖a - x‖ < 1) (hx : ‖x‖ = 1) : ‖a‖ ≤ 1 := by
  have := um_add_le h.le hx.le
  rwa [sub_add_cancel] at this

private theorem diff_lt {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) : ‖a - b‖ < 1 := by
  have := um_sub_lt ha hb
  rwa [sub_sub_sub_cancel_right] at this

private theorem half_lt (h2 : ‖(2 : K)‖ = 1) {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) :
    ‖(2 : K)⁻¹ * (a + b) - x‖ < 1 := by
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have e : (2 : K)⁻¹ * (a + b) - x = (2 : K)⁻¹ * ((a - x) + (b - x)) := by
    field_simp; ring
  rw [e, norm_mul, norm_inv, h2, inv_one, one_mul]
  exact um_add_lt ha hb

private theorem key (h2 : ‖(2 : K)‖ = 1) (γ : Kˣ) (x : K) (A B : Matrix (Fin 2) (Fin 2) K) (hγ : ‖(γ : K)‖ = 1) (hx : ‖x‖ = 1)
    (a00 : ‖A 0 0 - 1‖ < 1) (a11 : ‖A 1 1 - x‖ < 1) (a10 : ‖A 1 0‖ < 1) (a01 : ‖A 0 1‖ ≤ 1)
    (b00 : ‖B 0 0 - 1‖ < 1) (b11 : ‖B 1 1 - x‖ < 1) (b10 : ‖B 1 0‖ < 1) (b01 : ‖B 0 1‖ ≤ 1) :
    (∀ i j, ‖mix γ A B i j‖ ≤ 1) ∧ (∀ i, ‖mix γ A B i i - ![x, 1, x, 1] i‖ < 1) ∧
    (∀ i j, i ≠ j → wt i j ∉ vV → ‖mix γ A B i j‖ < 1) ∧
    (‖A 0 1‖ = 1 → ‖mix γ A B 1 0‖ = 1 ∨ (‖mix γ A B 1 2‖ = 1 ∧ ‖mix γ A B 3 0‖ = 1)) := by
  have hh : ∀ y : K, ‖(2 : K)⁻¹ * y‖ = ‖y‖ := fun y => by rw [norm_mul, norm_inv, h2, inv_one, one_mul]
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have p : ‖A 1 0 / γ‖ < 1 := by rwa [norm_div, hγ, div_one]
  have p' : ‖-(A 1 0 / γ)‖ < 1 := by rwa [norm_neg]
  have qe : ‖γ * A 0 1‖ = ‖A 0 1‖ := by rw [norm_mul, hγ, one_mul]
  have q : ‖γ * A 0 1‖ ≤ 1 := qe ▸ a01
  have q' : ‖-(γ * A 0 1)‖ ≤ 1 := by rwa [norm_neg]
  have c00 := le_of_cong a00 norm_one
  have c11 := le_of_cong a11 hx
  have d00 := le_of_cong b00 norm_one
  have d11 := le_of_cong b11 hx
  have e01 : ‖mix γ A B 0 1‖ < 1 := (hh _).trans_lt (um_sub_lt p b10)
  have e02 : ‖mix γ A B 0 2‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e03 : ‖mix γ A B 0 3‖ < 1 := (hh _).trans_lt (um_add_lt p b10)
  have e13 : ‖mix γ A B 1 3‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e20 : ‖mix γ A B 2 0‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e21 : ‖mix γ A B 2 1‖ < 1 := (hh _).trans_lt (um_sub_lt p' b10)
  have e23 : ‖mix γ A B 2 3‖ < 1 := (hh _).trans_lt (um_add_lt p' b10)
  have e31 : ‖mix γ A B 3 1‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e00 : ‖mix γ A B 0 0‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e11 : ‖mix γ A B 1 1‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e22 : ‖mix γ A B 2 2‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e33 : ‖mix γ A B 3 3‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e10 : ‖mix γ A B 1 0‖ ≤ 1 := (hh _).trans_le (um_sub_le q b01)
  have e12 : ‖mix γ A B 1 2‖ ≤ 1 := (hh _).trans_le (um_sub_le q' b01)
  have e30 : ‖mix γ A B 3 0‖ ≤ 1 := (hh _).trans_le (um_add_le q b01)
  have e32 : ‖mix γ A B 3 2‖ ≤ 1 := (hh _).trans_le (um_add_le q' b01)
  refine ⟨fun i j => ?_, fun i => ?_, fun i j hij hw => ?_, fun h => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [e00, e01.le, e02.le, e03.le, e10, e11, e12, e13.le, e20.le, e21.le, e22, e23.le, e30, e31.le, e32, e33]
  · fin_cases i
    exacts [half_lt h2 a11 b11, half_lt h2 a00 b00, half_lt h2 a11 b11, half_lt h2 a00 b00]
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact (hw (by decide)).elim
      | assumption
  · have m10 : mix γ A B 1 0 = (2 : K)⁻¹ * (γ * A 0 1 - B 0 1) := rfl
    have m12 : mix γ A B 1 2 = (2 : K)⁻¹ * (-(γ * A 0 1) - B 0 1) := rfl
    have m30 : mix γ A B 3 0 = (2 : K)⁻¹ * (γ * A 0 1 + B 0 1) := rfl
    have s : mix γ A B 1 0 + mix γ A B 3 0 = γ * A 0 1 := by
      rw [m10, m30]; field_simp; ring
    have n : ‖mix γ A B 1 2‖ = ‖mix γ A B 3 0‖ := by
      rw [← norm_neg, m12, m30]; congr 1; ring
    rcases e10.eq_or_lt with h1 | h1
    · exact Or.inl h1
    rcases e30.eq_or_lt with h3 | h3
    · exact Or.inr ⟨n.trans h3, h3⟩
    have := um_add_lt h1 h3
    rw [s, qe, h] at this
    exact absurd this (lt_irrefl _)

end

theorem UpperTheory.mixMatrix_residue_properties :
    UpperTheory.V.Sd.S2.MixRes := by
  intro l hl l2 γ x A B hγ hx hA hB
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    have e : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; rfl
    rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hl.out Nat.prime_two).2 l2
  exact key h2 γ x A B hγ hx hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
end

section

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Sd.S2 Matrix

section

variable {k : Type} [Field k]

private def Pm (a b : k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) k :=
  Matrix.of (Sum.elim ![![0, a, 0, a], ![b, 0, -b, 0]] ![![0, -1, 0, 1], ![1, 0, 1, 0]])

private def Qm (a b : k) : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) k :=
  Matrix.of ![Sum.elim ![0, (2 * b)⁻¹] ![0, 2⁻¹], Sum.elim ![(2 * a)⁻¹, 0] ![-2⁻¹, 0],
    Sum.elim ![0, -(2 * b)⁻¹] ![0, 2⁻¹], Sum.elim ![(2 * a)⁻¹, 0] ![2⁻¹, 0]]

private def J4 (k : Type) [Field k] : M4 k := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private lemma QP {a b : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) : Qm a b * Pm a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;> field_simp <;> ring

private lemma PQ {a b : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) : Pm a b * Qm a b = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private lemma Qmix {a b : kˣ} (h2 : (2 : k) ≠ 0) (A B : Matrix (Fin 2) (Fin 2) k) :
    Qm (a : k) b * Matrix.fromBlocks A 0 0 B * Pm (a : k) b = mix (b / a) A B := by
  have ha := a.ne_zero
  have hb := b.ne_zero
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  delta mix
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm] <;> field_simp <;> ring

private lemma Qoff {a b : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    Qm a b * Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) k) (Matrix.diagonal ![a ^ 2, b ^ 2]) (1 : Matrix (Fin 2) (Fin 2) k)
      (0 : Matrix (Fin 2) (Fin 2) k) * Pm a b = Matrix.diagonal ![b, -a, -b, a] := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm] <;> field_simp <;> ring

private lemma gram (a b : k) :
    (Pm a b)ᵀ * Matrix.fromBlocks (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) (0 : Matrix (Fin 2) (Fin 2) k) (0 : Matrix (Fin 2) (Fin 2) k)
      ((a * b) • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k)) * Pm a b = (-2 * (a * b)) • J4 k := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [Pm, J4] <;> ring

private lemma adj_eq (Y : M4 k) : adj Y = -J4 k * Yᵀ * J4 k := by
  ext i j
  simp only [adj_apply, Matrix.mul_apply, Fin.sum_univ_four]
  delta sgn
  fin_cases i <;> fin_cases j <;>
    simp [J4, Fin.rev]

private lemma JJ : -J4 k * J4 k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J4, Matrix.mul_apply, Fin.sum_univ_four]

private lemma gsp {a b ν : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (X B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) (hB : (Pm a b)ᵀ * B * Pm a b = (-2 * (a * b)) • J4 k)
    (hX : Xᵀ * B * X = ν • B) : IsGSp ν (Qm a b * X * Pm a b) := by
  have hc : (-2 * (a * b)) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) (mul_ne_zero ha hb)
  have hPY : Pm a b * (Qm a b * X * Pm a b) = X * Pm a b := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, PQ h2 ha hb, Matrix.one_mul]
  generalize Qm a b * X * Pm a b = Y at hPY
  have h1 : (-2 * (a * b)) • (Yᵀ * J4 k * Y) = (-2 * (a * b)) • (ν • J4 k) := by
    calc _ = Yᵀ * ((Pm a b)ᵀ * B * Pm a b) * Y := by rw [hB, Matrix.mul_smul, Matrix.smul_mul]
      _ = (Pm a b * Y)ᵀ * B * (Pm a b * Y) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Pm a b)ᵀ * (Xᵀ * B * X) * Pm a b := by
        rw [hPY]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hX, Matrix.mul_smul, Matrix.smul_mul, hB, smul_comm]
  have h3 : Yᵀ * J4 k * Y = ν • J4 k := smul_right_injective _ hc h1
  change adj Y * Y = ν • (1 : M4 k)
  rw [adj_eq]
  calc _ = -J4 k * (Yᵀ * J4 k * Y) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h3, Matrix.mul_smul, JJ]

end

theorem UpperTheory.symmetric_square_mixed_exists :
    UpperTheory.V.Sd.S2.MixEx := by
  intro k Γ₀ Γ _ _ _ j t α β ρ μ h2 hj hi ht hsq hdet hαβ
  have ha := α.ne_zero
  have hb := β.ne_zero
  let e : Γ₀ ≃* j.range := MonoidHom.ofInjective hj
  have he : ∀ h, ((e h : j.range) : Γ) = j h := fun h => rfl
  let r : j.range →* GL (Fin 2) k := ρ.comp e.symm.toMonoidHom
  have hr : ∀ h, r (e h) = ρ h := fun h => by simp [r]
  obtain ⟨I, hI1, hI2⟩ := UpperTheory.V.AlgebraTools.indTwo j.range t hi ht r
  have hS := UpperTheory.V.AlgebraTools.indSymp j.range t hi ht r μ I (by
    intro h
    obtain ⟨h, rfl⟩ := e.surjective h
    rw [hr, he, ← hdet, Matrix.GeneralLinearGroup.val_det_apply]) hI1 hI2
  let M : Γ →* M4 k :=
    { toFun := fun g => Qm (α : k) β * (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * Pm (α : k) β
      map_one' := by rw [map_one, Units.val_one, Matrix.mul_one, QP h2 ha hb]
      map_mul' := by
        intro x y
        rw [map_mul, Units.val_mul]
        calc _ = Qm (α : k) β * (I x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * (Pm (α : k) β * Qm (α : k) β) *
              (I y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * Pm (α : k) β := by
                rw [PQ h2 ha hb]; simp only [Matrix.mul_assoc, Matrix.one_mul]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hM : ∀ g, ((M.toHomUnits g : GL (Fin 4) k) : M4 k) =
      Qm (α : k) β * (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * Pm (α : k) β := fun g => rfl
  refine ⟨M.toHomUnits, ⟨h2, hj, hi, ht, hsq, ?_, ?_⟩, ?_⟩
  · intro h h' hh
    have := hI1 (e h) (e h') hh
    rw [he, hr, hr] at this
    rw [hM, this, Qmix h2]
  · obtain ⟨u, hu⟩ := Subgroup.mul_self_mem_of_index_two hi t
    have := hI2 (e u) hu
    rw [hr, hsq u hu] at this
    rw [hM, this, Qoff h2 ha hb]
  · intro g
    rw [hM]
    refine gsp h2 ha hb _ _ ?_ (hS g)
    rw [← hαβ, Units.val_mul]
    exact gram _ _
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem norm_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ‖(2 : Qbar l)‖ = 1 := by
  have h : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by simp [map_ofNat]
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl

private theorem alg {A : Type} [CommGroup A] (d x o p q f : A) (k e : ℕ)
    (h : d ^ 2 * (x ^ k * q * f) = x * o⁻¹ * q * (x ^ (e : ℤ) * p)) :
    d ^ 2 = x ^ ((e : ℤ) + 1 - k) * (o⁻¹ * p * f⁻¹) := by
  rw [eq_mul_inv_of_mul_eq h, zpow_sub, zpow_add, zpow_one, zpow_natCast, zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

private theorem pow_one_of_dvd {A : Type} [Monoid A] {x : A} {a : ℕ} (h : x ^ a = 1) {n : ℕ} (hn : a ∣ n) : x ^ n = 1 := by
  obtain ⟨b, rfl⟩ := hn
  rw [pow_mul, h, one_pow]

theorem UpperTheory.induced_deletion_condition :
    UpperTheory.V.Sd.S2.IndDel := by
  intro Ω _ _ _ l hl c D T k₀ _ _ φ ι k t r α β R δ h
  have hG := h.hyp.good
  have hchi : ∀ g : G T.F Ω, up (chiO ℚ Ω l c.O) (resQ T.F g) = cycBar T.F Ω l g := fun g => Units.ext rfl
  have key : ∀ g : G T.F Ω, δ g ^ 2 = cycBar T.F Ω l g ^ ((D.e : ℤ) + 1 - k) *
      ((up D.om (resQ T.F g))⁻¹ * up D.ψ (resQ T.F g) * (φ (resQ T.F g))⁻¹) := by
    intro g
    apply alg _ _ _ _ (up D.ξ (resQ T.F g))
    have h1 := h.δ_sq g
    have h2 : up D.th (resQ T.F g) = cycBar T.F Ω l g * (up D.om (resQ T.F g))⁻¹ * up D.ξ (resQ T.F g) *
        (cycBar T.F Ω l g ^ (D.e : ℤ) * up D.ψ (resQ T.F g)) := by
      rw [← hchi]
      simp only [up, Raw.th, Raw.al, Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
        MonoidHom.zpow_apply, map_mul, map_inv, map_zpow]
    rw [← h2, ← h1]
    rfl
  obtain ⟨m, hm, hψ⟩ := h.hyp.deep
  have hl1 : 1 < l := hl.out.one_lt
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [Nat.coprime_zero_right] at hm; omega
    · exact h0
  have hφ : ∀ g, φ g ^ 2 = 1 := by
    intro g
    by_cases hg : g ∈ k₀.fixingSubgroup
    · rw [h.hyp.φ_in g hg, one_pow]
    · rw [h.hyp.φ_out g hg]; simp
  have hφI : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.F) A, φ (resQ T.F s) = 1 := by
    intro A hA s hs
    apply h.hyp.φ_in
    apply h.hyp.spl A hA
    exact hs.1
  have hcont : Continuous (resQ T.F) := by
    haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
    exact (galEmbTop ℚ T.F Ω).1.continuous
  have hup : ∀ (χ : G ℚ Ω →* c.Oˣ) g, χ g = 1 → up χ g = 1 := fun χ g hg => by
    simp only [up, MonoidHom.comp_apply, hg, map_one]
  refine ⟨(D.e : ℤ) + 1 - k, (l - 1) * m * 2, (D.ψ.ker ⊓ D.om.ker).comap (resQ T.F), ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos (by omega) hm0) two_pos
  · intro g
    have a1 : up D.om (resQ T.F g) ^ (l - 1) = 1 := by
      have := DFunLike.congr_fun hG.om_pow (resQ T.F g)
      rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      simp only [up, MonoidHom.comp_apply, ← map_pow, this, map_one]
    have a2 : up D.ψ (resQ T.F g) ^ m = 1 := by
      simp only [up, MonoidHom.comp_apply, ← map_pow, hψ g, map_one]
    have b1 := (pow_one_of_dvd a1 (n := (l - 1) * m * 2) ⟨m * 2, by ring⟩)
    have b2 := (pow_one_of_dvd a2 (n := (l - 1) * m * 2) ⟨(l - 1) * 2, by ring⟩)
    have b3 := (pow_one_of_dvd (hφ (resQ T.F g)) (n := (l - 1) * m * 2) ⟨(l - 1) * m, by ring⟩)
    rw [key g, zpow_neg, mul_inv_cancel_comm, mul_pow, mul_pow, inv_pow, inv_pow, b1, b2, b3]
    simp
  · exact (hG.psi_open.inter h.chars.om_open).preimage hcont
  · intro A hA s hs
    have fin : D.ψ (resQ T.F s) = 1 → D.om (resQ T.F s) = 1 → δ s ^ 2 = cycBar T.F Ω l s ^ ((D.e : ℤ) + 1 - k) := by
      intro h1 h2
      rw [key s, hup _ _ h1, hup _ _ h2, hφI A hA s hs]
      simp
    refine ⟨fun hU => fin hU.1 hU.2, fun hc => ?_⟩
    have hc' : cycZ ℚ Ω l (resQ T.F s) = 1 := hc
    have hb : cycBar T.F Ω l s = 1 := by
      simp only [cycBar, MonoidHom.comp_apply, hc, map_one]
    have hb' : cycBar ℚ Ω l (resQ T.F s) = 1 := hb
    have ho : D.om (resQ T.F s) = 1 := by
      rw [h.chars.om, hb']
      simp [Cong]
    have hP : D.Psi (resQ T.F s) = D.ψ (resQ T.F s) := by
      simp only [Raw.Psi, UpperTheory.V.Chr.Psi, chiO, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, hc', map_one,
        one_zpow, one_mul]
    have hp : D.ψ (resQ T.F s) = 1 := by
      apply UpperTheory.teichmuller_character_spec l c _ m hm (hψ s)
      have := congrFun (congrFun (h.hyp.ok.ineL A hA s hs) 1) 1
      rw [← hP]
      simpa [Raw.rbar, Raw.r0, diagRep, Raw.ps] using this
    have h2 := fin hp ho
    rw [hb, one_zpow] at h2
    have h3 : (δ s : Qbar l) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    rcases sq_eq_one_iff.1 h3 with h4 | h4
    · exact Units.ext h4
    · have h5 := h.δ_one s
      rw [Cong, h4, Units.val_one, show (-1 - 1 : Qbar l) = -2 by norm_num, norm_neg, norm_two l hG.l_odd] at h5
      exact absurd h5 (lt_irrefl _)
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd.S2

private theorem exists_sign_character_index_two {Γ R : Type} [Group Γ] [CommRing R] (H : Subgroup Γ) (h : H.index = 2) :
    ∃ φ : Γ →* Rˣ, (∀ g ∈ H, φ g = 1) ∧ ∀ g ∉ H, φ g = -1 := by
  classical
  refine ⟨MonoidHom.mk' (fun g => if g ∈ H then 1 else -1) fun a b => ?_, fun g hg => if_pos hg, fun g hg => if_neg hg⟩
  by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [Subgroup.mul_mem_iff_of_index_two h, ha, hb]

theorem UpperTheory.exists_quadratic_character_of_subgroup_index_two :
    UpperTheory.V.Sd.S2.HypEx := by
  intro Ω _ _ _ l _ c D T hg hok htwo hdeep
  obtain ⟨k₀, hdeg, hreal, hsp, hps⟩ := htwo.quad
  haveI : FiniteDimensional ℚ k₀ := Module.finite_of_finrank_pos (by omega)
  haveI hnf : NumberField k₀ := {}
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
  obtain ⟨hE, hO, hI⟩ := galEmbTop ℚ k₀ Ω
  have hfix : galOf ℚ k₀ Ω = k₀.fixingSubgroup := by
    ext σ
    rw [mem_galOf, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  have hr : (resQ k₀).range = k₀.fixingSubgroup := (range_galEmb ℚ k₀ Ω).trans hfix
  have hidx : k₀.fixingSubgroup.index = 2 := by rw [← hfix, hI, hdeg]
  obtain ⟨φ, h1, h2⟩ := exists_sign_character_index_two (R := PadicAlgCl l) k₀.fixingSubgroup hidx
  refine ⟨k₀, hnf, hreal, φ, ⟨hg, hok, htwo, hdeep, hdeg, ?_, ?_, hps, h1, h2⟩, hr, hidx, hE, ?_⟩
  · exact hsp 2 (by simp)
  · exact hsp l (by simp)
  · rw [← MonoidHom.coe_range, hr, ← hfix]
    exact hO
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

theorem UpperTheory.exists_ribet_lattice :
    UpperTheory.V.Sd.S2.RibOf := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r hyp hch hd u hu
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois k₀ Ω := {}
  have hc : Continuous (resQ k₀ : G k₀ Ω →* G ℚ Ω) := by
    have h := (galEmbTop ℚ k₀ Ω).1.continuous
    have e : (resQ k₀ : G k₀ Ω →* G ℚ Ω) = galEmb ℚ k₀ Ω := by
      ext σ x
      rw [galEmb_apply]; rfl
    rw [e]; exact h
  let H : Subgroup (G k₀ Ω) := T.F.fixingSubgroup.comap (resQ k₀)
  have hHo : IsOpen (H : Set (G k₀ Ω)) := T.F.fixingSubgroup_isOpen.preimage hc
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 (H.isClosed_of_isOpen hHo).isCompact
  have hg : resQ T.F T.g0 ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact T.g0.commutes ⟨x, hx⟩
  have huH : u ∈ H := by
    show resQ k₀ u ∈ T.F.fixingSubgroup
    rw [hu]; exact mul_mem hg hg
  obtain ⟨ρ', ⟨g, hρ⟩, q1, q2, q3, s, q4⟩ := ribetLat l H (r.comp H.subtype) 1 (((up D.ξ).comp (resQ k₀)).comp H.subtype)
    (hd.cont.comp continuous_subtype_val) (hd.irr H hHo) (fun s => ⟨by simp, hch.unit _ _⟩)
    (fun s i => by
      have := hd.res s i
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply,
        Subgroup.coe_subtype] using this) ⟨u, huH⟩ (by
      have := hch.sq
      rw [← hu] at this
      exact this)
  have e : ∀ s : H, ((MulAut.conj g).toMonoidHom.comp r) s = ρ' s := fun s => (hρ s).symm
  refine ⟨(MulAut.conj g).toMonoidHom.comp r, ⟨g, fun _ => rfl⟩, ?_, ?_, fun h hh => ?_, s, s.2, ?_⟩
  · rw [e ⟨u, huH⟩]; exact q1
  · rw [e ⟨u, huH⟩]; exact q2
  · rw [e ⟨h, hh⟩]; exact q3 ⟨h, hh⟩
  · rw [e s]; exact q4
end
