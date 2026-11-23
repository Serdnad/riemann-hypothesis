module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle206
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle168
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle212
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle213
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

section

open scoped ComplexOrder

namespace GlobalTheory.MajPosCpx

theorem gram_sub_eq {n r a b : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) (g : Fin b → Fin r) (R : Matrix (Fin a) (Fin b) ℂ)
    (hR : ∀ i j, (X.conjTranspose * J * Y) (f i) (g j) = R i j) :
    (X.submatrix id f).conjTranspose * J * (Y.submatrix id g) = R := by
  ext i j; rw [← hR]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem mul_submatrix_id {n r a : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) : u * X.submatrix id f = (u * X).submatrix id f := by
  ext i j; simp [Matrix.mul_apply]

theorem exists_unip_conj_unitary : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 → Y.conjTranspose * J * Y = 0 → X.conjTranspose * J * Y = 1 →
    ∀ (c : GL (Fin n) ℂ) (ε : Fin n → Bool), (c.1).conjTranspose * J * c.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GL (Fin n) ℂ) (N : Matrix (Fin r) (Fin r) ℂ),
        (u.1).conjTranspose * J * u.1 = J ∧ u.1 * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u.1 v - v = Matrix.mulVec X w) ∧
        ∃ y₀ : GL (Fin d) ℂ, ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
          let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
          let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
          let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
          let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
          let M : Matrix (Fin n) (Fin n) ℂ := (c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1
          M.conjTranspose * M = 1 := by
  intro n r J hJ X Y hXX hYY hXY c ε hc l d h
  set Dg : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if ε i then 1 else -1) with hDg
  have hDD : Dg * Dg = 1 := by
    rw [hDg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> norm_num
  have hcc : c.1 * (c⁻¹).1 = 1 := Units.mul_inv c
  have hcc' : (c⁻¹).1 * c.1 = 1 := Units.inv_mul c
  have hcH : (c⁻¹).1.conjTranspose * (c.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hcc, Matrix.conjTranspose_one]
  have hJc : J = (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 := by
    have e : (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 =
        ((c⁻¹).1.conjTranspose * (c.1).conjTranspose) * J * (c.1 * (c⁻¹).1) := by
      rw [← hc]; simp only [Matrix.mul_assoc]
    rw [e, hcH, hcc, Matrix.one_mul, Matrix.mul_one]
  set θ : Matrix (Fin n) (Fin n) ℂ := c.1 * Dg * (c⁻¹).1 with hθ
  have hθθ : θ * θ = 1 := by
    simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul, hcc]
  have hQ : J * θ = (c⁻¹).1.conjTranspose * (c⁻¹).1 := by
    rw [hJc]; simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul]
  have hQpd : (J * θ).PosDef := by
    rw [hQ]; exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (c⁻¹).isUnit)
  set X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₁
  set Y₁ : Matrix (Fin n) (Fin l) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₁
  set Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩ with hXb
  set Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩ with hYb
  set X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₂
  set Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₂
  have w11 : X₁.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have w1b : X₁.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have wbb : Xb.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have v11 : X₁.conjTranspose * J * Y₁ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have v1b : X₁.conjTranspose * J * Yb = 0 :=
    gram_sub_eq J X Y _ _ 0 (fun i j => by
      rw [hXY, Matrix.one_apply, if_neg]
      · rfl
      · simp only [Fin.ext_iff]; omega)
  have ybb : Yb.conjTranspose * J * Yb = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have vbb : Xb.conjTranspose * J * Yb = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w22 : X₂.conjTranspose * J * X₂ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have y22 : Y₂.conjTranspose * J * Y₂ = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have v22 : X₂.conjTranspose * J * Y₂ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w21 : X₂.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  obtain ⟨u₂, A, hu₂J, hu₂X₁, hu₂Xb, hu₂Yb, hu₂v, hA⟩ :=
    GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal n l d J (J * θ) hJ hQpd X₁ Y₁ Xb Yb w11 w1b wbb v11 v1b ybb vbb
  obtain ⟨u₁, hu₁J, hu₁X₂, hu₁v, hθX₂⟩ := GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant n (l + d) J θ hJ hθθ hQpd X₂ Y₂ w22 y22 v22
  have hu₁X₁ : u₁.1 * X₁ = X₁ := by
    have e : X₁ = X₂.submatrix id (fun j : Fin l => ⟨j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  have hu₁Xb : u₁.1 * Xb = Xb := by
    have e : Xb = X₂.submatrix id (fun j : Fin d => ⟨l + j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  set u : GL (Fin n) ℂ := u₁ * u₂ with hu
  have huv : u.1 = u₁.1 * u₂.1 := Units.val_mul u₁ u₂
  have huJ : (u.1).conjTranspose * J * u.1 = J := by
    have e : (u₂.1).conjTranspose * (u₁.1).conjTranspose * J * (u₁.1 * u₂.1) =
        (u₂.1).conjTranspose * ((u₁.1).conjTranspose * J * u₁.1) * u₂.1 := by simp only [Matrix.mul_assoc]
    rw [huv, Matrix.conjTranspose_mul, e, hu₁J, hu₂J]
  have huX₁ : u.1 * X₁ = X₁ := by rw [huv, Matrix.mul_assoc, hu₂X₁, hu₁X₁]
  have huXb : u.1 * Xb = Xb + X₁ * A := by
    rw [huv, Matrix.mul_assoc, hu₂Xb, Matrix.mul_add, hu₁Xb, ← Matrix.mul_assoc, hu₁X₁]
  have huYb : u.1 * Yb = u₁.1 * Yb := by rw [huv, Matrix.mul_assoc, hu₂Yb]
  have huP : ∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
      ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u.1 v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a := by
    intro v hv
    have h1 : Matrix.mulVec (X₁.conjTranspose * J) v = 0 := by
      funext i; exact congrFun hv ⟨i.val, by omega⟩
    set a := Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v) with ha
    have h2 : Matrix.mulVec (X₂.conjTranspose * J) (v + Matrix.mulVec X₁ a) = 0 := by
      rw [Matrix.mulVec_add, hv, Matrix.mulVec_mulVec, w21, Matrix.zero_mulVec, add_zero]
    obtain ⟨w, hw⟩ := hu₁v _ h2
    refine ⟨w, a, ?_⟩
    rw [huv, ← Matrix.mulVec_mulVec, hu₂v v h1, ← hw]
    abel
  obtain ⟨N, hN, hNs, hNp⟩ := GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse n r J X hXX l d h u.1 A huX₁ huXb huP
  obtain ⟨hθX', hHpd⟩ := GlobalTheory.T.hermitian_flag_complement_posDef_factorization n r J θ hJ hQpd X Y hXY l d h u₁.1 A hθX₂ hA
  set H : Matrix (Fin d) (Fin d) ℂ := Xb.conjTranspose * (J * θ) * (Xb + X₁ * A) with hHdef
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' d H hHpd
  have hθu : θ * u.1 * Xb = u.1 * Yb * H := by
    rw [Matrix.mul_assoc, huXb, hθX', huYb]
  have hy1 : (y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hHy : H = (y₀⁻¹).1.conjTranspose * (y₀⁻¹).1 := by
    calc H = ((y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose) * H * (y₀.1 * (y₀⁻¹).1) := by
          rw [hy1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (y₀⁻¹).1.conjTranspose * ((y₀.1).conjTranspose * H * y₀.1) * (y₀⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hy₀, Matrix.mul_one]
  have hHinv : H * (y₀.1 * (y₀.1).conjTranspose) = 1 := by
    calc H * (y₀.1 * (y₀.1).conjTranspose) = (y₀⁻¹).1.conjTranspose * ((y₀⁻¹).1 * y₀.1) * (y₀.1).conjTranspose := by
          rw [hHy]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.inv_mul, Matrix.mul_one, hy1]
  have huJ' : (u.1).conjTranspose * J = J * (u⁻¹).1 := by
    calc (u.1).conjTranspose * J = (u.1).conjTranspose * J * (u.1 * (u⁻¹).1) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = ((u.1).conjTranspose * J * u.1) * (u⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = J * (u⁻¹).1 := by rw [huJ]
  have hθuY : θ * u.1 * Yb = u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc θ * u.1 * Yb = θ * u.1 * Yb * (H * (y₀.1 * (y₀.1).conjTranspose)) := by rw [hHinv, Matrix.mul_one]
      _ = θ * (θ * u.1 * Xb) * (y₀.1 * (y₀.1).conjTranspose) := by rw [hθu]; simp only [Matrix.mul_assoc]
      _ = (θ * θ) * u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hθθ, Matrix.one_mul]
  have hPX : (u.1).conjTranspose * (J * θ) * u.1 * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Xb = ((u.1).conjTranspose * J) * (θ * u.1 * Xb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Yb * H := by rw [huJ', hθu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one, hHy]
  have hPY : (u.1).conjTranspose * (J * θ) * u.1 * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Yb = ((u.1).conjTranspose * J) * (θ * u.1 * Yb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Xb * (y₀.1 * (y₀.1).conjTranspose) := by rw [huJ', hθuY]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one]
  have hPH : ((u.1).conjTranspose * (J * θ) * u.1).conjTranspose = (u.1).conjTranspose * (J * θ) * u.1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQpd.1.eq]
    simp only [Matrix.mul_assoc]
  refine ⟨u, N, huJ, hN, hNs, fun v hv => hNp v hv, y₀, fun k hk => ?_⟩
  intro Xb' Yb' m G M
  have hG : G.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * G = (u.1).conjTranspose * (J * θ) * u.1 :=
    GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary n d J ((u.1).conjTranspose * (J * θ) * u.1) Xb Yb y₀ hJ hPH wbb ybb vbb hPX hPY k hk
  show ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) = 1
  have e1 : ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) =
      (c.1).conjTranspose * ((u⁻¹).1.conjTranspose *
        (G.conjTranspose * ((u.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * u.1) * G) * (u⁻¹).1) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e1, ← hQ, hG]
  have e2 : (c.1).conjTranspose * ((u⁻¹).1.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * (u⁻¹).1) * c.1 =
      (c.1).conjTranspose * ((u.1 * (u⁻¹).1).conjTranspose * (J * θ) * (u.1 * (u⁻¹).1)) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hQ]
  have e3 : (c.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * c.1 =
      ((c⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * c.1) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e3, hcc', Matrix.conjTranspose_one, Matrix.one_mul]

end GlobalTheory.MajPosCpx
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem filtered_identify_pairs {J : Type} [SmallCategory J] [IsFiltered J] (P : J ⥤ Type)
    (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (T : Finset (P.obj j × P.obj j)) (hT : ∀ p ∈ T, ι j p.1 = ι j p.2) :
    ∃ (k : J) (f : j ⟶ k), ∀ p ∈ T, P.map f p.1 = P.map f p.2 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | @insert p T hp ih =>
    obtain ⟨k1, f1, h1⟩ := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    obtain ⟨k2, f2, h2⟩ := hinj j p.1 p.2 (hT p (Finset.mem_insert_self p T))
    have e : f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) =
        f2 ≫ IsFiltered.rightToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) := by
      simpa only [Category.assoc] using
        IsFiltered.coeq_condition (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2)
    refine ⟨_, f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2), ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [e]
      simp only [Functor.map_comp_apply, h2]
    · simp only [Functor.map_comp_apply, h1 q hq]

theorem finsupp_mapDomain_eq_zero_at_stage (Λ : Type 1) [AddCommGroup Λ] (J : Type)
    [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hcompat : ∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (x : P.obj j →₀ Λ) (hx : Finsupp.mapDomain (ι j) x = 0) :
    ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  classical
  obtain ⟨k, f, hf⟩ := filtered_identify_pairs P Q ι hinj j
    ((x.support ×ˢ x.support).filter (fun p => ι j p.1 = ι j p.2))
    (fun p hp => (Finset.mem_filter.mp hp).2)
  refine ⟨k, f, ?_⟩
  have hcomp : Finsupp.mapDomain (ι k) (Finsupp.mapDomain (P.map f) x) =
      Finsupp.mapDomain (ι j) x := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext a
    exact hcompat j k f a
  have hInj : Set.InjOn (ι k) (P.map f '' (x.support : Set (P.obj j))) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hcompat, hcompat] at hab
    exact hf (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)
  apply Finsupp.mapDomain_injOn _ hInj
  · intro b hb
    have := Finsupp.mapDomain_support (f := P.map f) (s := x) hb
    simpa using this
  · simp
  · rw [hcomp, hx, Finsupp.mapDomain_zero]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulUnramified

lemma eq_one_of_pow_eq_one_thick_affine (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (G : Over (Sp C)) [GrpObj G] (n : ℕ)
    (hn : IsUnit (n : C)) (R : CommRingCat.{0}) (g : Spec R ⟶ Sp C) (z : Over.mk g ⟶ G)
    (hz : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g), j ≫ z = 1)
    (hzn : z ^ n = 1) : z = 1 := by
  let φ : CommRingCat.of C ⟶ R := Spec.preimage g
  let K : Ideal C := RingHom.ker π
  let J : Ideal R := Ideal.map φ.hom K
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* R ⧸ J :=
    (Ideal.quotientMap J φ.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ∀ c, ψ (π c) = q (φ c) := by
    intro c
    have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk K c := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
    rfl
  have hJ : RingHom.ker q = J := Ideal.mk_ker
  have hJsq : J ^ 2 = ⊥ := by
    simp only [J, ← Ideal.map_pow]
    change Ideal.map φ.hom (RingHom.ker π ^ 2) = ⊥
    rw [hsq, Ideal.zero_eq_bot, Ideal.map_bot]
  let T₀ : Over (Sp C₀) := Over.mk (spMap ψ)
  have hw : Spec.map (CommRingCat.ofHom q) ≫ g = T₀.hom ≫ spMap π := by
    rw [← Spec.map_preimage g]
    simp only [T₀, spMap, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext c
    exact (hψ c).symm
  let j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g := Over.homMk (Spec.map (CommRingCat.ofHom q)) hw
  have hsurj : Function.Surjective j.left := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap q)
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker q ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hJ, hJsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have hker : RingHom.ker (CommRingCat.ofHom q).hom ^ 2 = ⊥ := by
    change RingHom.ker q ^ 2 = ⊥
    rw [hJ, hJsq]
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  exact eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq (CommRingCat.ofHom q) hker) n hn' z
    (hz T₀ j) hzn

end GlobalTheory.MulUnramified

namespace GlobalTheory.MulUnramified

theorem eq_one_of_pow_eq_one_thick : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  intro C C₀ _ _ π hπ hsq G _ n hn T z hz hzn
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i ↦ ?_
  let k : T.left.affineOpenCover.I₀ := i
  let f : Over.mk (T.left.affineOpenCover.f k ≫ T.hom) ⟶ T := Over.homMk (T.left.affineOpenCover.f k) rfl
  have hfz : (f ≫ z) ^ n = 1 := by
    rw [← MonObj.comp_pow, hzn, comp_one]
  have h := eq_one_of_pow_eq_one_thick_affine C C₀ π hπ hsq G n hn _ _ (f ≫ z)
    (fun T₀ j ↦ by rw [← Category.assoc]; exact hz T₀ _) hfz
  have h' := congrArg (·.left) (h.trans (comp_one f).symm)
  simp only [Over.comp_left] at h'
  exact h'

end GlobalTheory.MulUnramified
end

section


theorem _root_.GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix : ∀ (R : Type) [CommRing R] (I : Ideal R), IsLocalRing (R ⧸ I) → ∀ (m k : ℕ), 0 < m →
    ∀ (O : Type) [Ring O] [Algebra R O] (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)), Function.Surjective φ →
    (∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) →
    ∀ (M N : Type) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
      [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N],
    (M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → (N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → Nonempty (M ≃ₗ[O] N) := by
  first | (exact @GlobalTheory.MoritaLocal.morita_local) | (exact GlobalTheory.MoritaLocal.morita_local) | (intros; apply GlobalTheory.MoritaLocal.morita_local  <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem frobLift_localization :
    ∀ (p : ℕ) [Fact p.Prime] {B Kt : Type} [CommRing B] [CommRing Kt] [Algebra B Kt]
      (S : Submonoid B) [IsLocalization S Kt] (F : B →+* B), (p : B) ^ 2 = 0 →
      (∀ z, ∃ w, F z = z ^ p + p * w) →
      ∃ F' : Kt →+* Kt, (∀ b, F' (algebraMap B Kt b) = algebraMap B Kt (F b)) ∧
        ∀ z, ∃ w, F' z = z ^ p + p * w := by
  intro p _ B Kt _ _ _ S _ F hp2 hF
  have hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s) := by
    intro s
    obtain ⟨w, hw⟩ := hF (s : B)
    have hu : IsUnit (algebraMap B Kt (s : B) ^ p) :=
      (IsLocalization.map_units Kt s).pow p
    have hn : IsNilpotent ((p : Kt) * algebraMap B Kt w) := by
      refine ⟨2, ?_⟩
      have : (p : Kt) ^ 2 = 0 := by
        have := congrArg (algebraMap B Kt) hp2
        simpa using this
      rw [mul_pow, this, zero_mul]
    have := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
    rw [add_comm] at this
    simpa [RingHom.comp_apply, hw, map_add (f := _), map_mul, map_pow, map_natCast] using this
  refine ⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩
  intro z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  set z := IsLocalization.mk' Kt b s with hz
  set F' : Kt →+* Kt := IsLocalization.lift hunit
  have hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c) := fun c => by
    simp [F', IsLocalization.lift_eq]
  have hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b := IsLocalization.mk'_spec Kt b s
  obtain ⟨v, hv⟩ := hF b
  obtain ⟨u, hu⟩ := hF (s : B)
  have key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) =
      algebraMap B Kt b ^ p + p * algebraMap B Kt v := by
    have := congrArg F' hspec
    rw [map_mul, hF', hF', hu, hv] at this
    simpa [map_add (f := _), map_mul, map_pow, map_natCast] using this
  obtain ⟨t, ht⟩ := (IsLocalization.map_units Kt s).pow p
  refine ⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩
  have hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p := by
    rw [← mul_pow, hspec]
  have h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u) := by
    rw [ht]; linear_combination key - hzs
  calc F' z = z ^ p + (F' z - z ^ p) * (t : Kt) * ↑t⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]; ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.DI
end

section


theorem _root_.GlobalTheory.T.exists_primitive_element_separability_certificate : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F), IsTranscendenceBasis k ((↑) : s → F) → Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F → ∀ T : Finset F, ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧ ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧ ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)), U * minpoly (Algebra.adjoin k (s : Set F)) θ + V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) = Polynomial.C H ∧ ∀ x ∈ T, (H : F) * x ∈ Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  first | exact @GlobalTheory.SepPoint.exists_primitive_sep_certificate | exact GlobalTheory.SepPoint.exists_primitive_sep_certificate | (intros; apply GlobalTheory.SepPoint.exists_primitive_sep_certificate <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend : ∀ (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R), Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first | exact @GlobalTheory.finite_injective_localHom_and_extend | exact GlobalTheory.finite_injective_localHom_and_extend | (intros; apply GlobalTheory.finite_injective_localHom_and_extend <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_common_eigenvector_mem_of_commute : ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) K)), (∀ A ∈ S, ∀ B ∈ S, Commute A B) → ∀ (E : Submodule K (Fin n → K)), E ≠ ⊥ → (∀ A ∈ S, ∀ v ∈ E, A *ᵥ v ∈ E) → ∃ v ∈ E, v ≠ 0 ∧ ∀ A ∈ S, ∃ μ : K, A *ᵥ v = μ • v := by
  first | exact @GlobalTheory.matrix_exists_common_eigenvector_mem | exact GlobalTheory.matrix_exists_common_eigenvector_mem | (intros; apply GlobalTheory.matrix_exists_common_eigenvector_mem <;> assumption)
end

section


theorem _root_.GlobalTheory.T.etale_maximal_quotient_algebraic : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  first | (exact @GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (exact GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (intros; apply GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue  <;> assumption)
end
