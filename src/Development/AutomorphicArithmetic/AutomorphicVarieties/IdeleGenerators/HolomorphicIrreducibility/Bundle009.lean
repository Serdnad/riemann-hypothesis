module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle088
public import Mathlib.Data.Nat.Notation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle007
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

private theorem det_scalar_sub_symmetric_square (S : Type) [CommRing S] (x e : S) (g : Matrix (Fin 2) (Fin 2) S) :
    (Matrix.scalar (Fin 3) x - e • symSquareMatrixHom S g).det =
      x ^ 3 - e * (g.trace ^ 2 - g.det) * x ^ 2 + e * (g.trace ^ 2 - g.det) * (e * g.det) * x - (e * g.det) ^ 3 := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_three]
  simp [symSquareMatrixHom, Matrix.scalar_apply]
  ring

private noncomputable def a0F {S : Type} [CommRing S] (u : S) : S[X] :=
  X ^ 3 + C (-u) * X ^ 2 + C u * X ^ 1 + C (-1) * X ^ 0

private theorem adjoint_square_charpoly (S : Type) [CommRing S] (e : S) (g : Matrix (Fin 2) (Fin 2) S) (he : e * g.det = 1) :
    (e • symSquareMatrixHom S g).charpoly = a0F (e * g.trace ^ 2 - 1) := by
  have h : Matrix.charmatrix (e • symSquareMatrixHom S g) = Matrix.scalar (Fin 3) X - C e • symSquareMatrixHom S[X] (g.map C) := by
    unfold Matrix.charmatrix
    congr 1
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom, map_ofNat]
  have hd : (g.map C).det = C g.det := by
    simp [Matrix.det_fin_two]
  have ht : (g.map C).trace = C g.trace := by
    simp [Matrix.trace_fin_two]
  have he' : C e * C g.det = 1 := by rw [← map_mul, he, map_one]
  rw [Matrix.charpoly, h, det_scalar_sub_symmetric_square, hd, ht, mul_sub (C e), he']
  simp only [a0F, map_sub, map_mul, map_pow, map_neg, map_one]
  ring

private theorem adjoint_charpoly_roots {S : Type} [Field S] (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) :
    a0F ((a * b)⁻¹ * (a + b) ^ 2 - 1) = (X - C (a / b)) * (X - C 1) * (X - C (b / a)) := by
  have h1 : (a * b)⁻¹ * (a + b) ^ 2 - 1 = a / b + 1 + b / a := by field_simp; ring
  have h2 : C (a / b) * C (b / a) = 1 := by
    rw [← map_mul, show a / b * (b / a) = 1 by field_simp, map_one]
  rw [h1]
  simp only [a0F, map_add (f := _), map_neg, map_one]
  linear_combination (1 - X) * h2

private theorem quadratic_charpoly_coeff_difference {S : Type} [CommRing S] [Nontrivial S] (g : Matrix (Fin 2) (Fin 2) S) (a b : S) :
    g.charpoly.coeff 1 - ((X - C a) * (X - C b)).coeff 1 = -(g.trace - (a + b)) ∧
    g.charpoly.coeff 0 - ((X - C a) * (X - C b)).coeff 0 = g.det - a * b := by
  have h : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
    simp only [map_add (f := _), map_mul]; ring
  rw [h, Matrix.charpoly_fin_two]
  constructor
  · simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C]
    simp; ring
  · simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_zero, coeff_C]
    simp

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1

private theorem Rl.left {x y : K} (h : Rl x y) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.2.le h.1)

private theorem Rl.mul {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x * z) (y * w) := by
  refine ⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩
  rw [show x * z - y * w = x * (z - w) + (x - y) * w by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1

private theorem Rl.inv {x y : K} (h : Rl x y) (hy : ‖y‖ = 1) : Rl x⁻¹ y⁻¹ := by
  have hx : ‖x‖ = 1 := by
    refine le_antisymm h.left (not_lt.mp fun hx => ?_)
    have := IsUltrametricDist.norm_add_le_max x (-(x - y))
    rw [norm_neg, show x + -(x - y) = y by ring, hy] at this
    exact absurd (max_lt hx h.2) (not_lt.mpr this)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  refine ⟨by rw [norm_inv, hy, inv_one], ?_⟩
  rw [show x⁻¹ - y⁻¹ = -(x - y) * (x⁻¹ * y⁻¹) by field_simp; ring, norm_mul, norm_mul, norm_neg, norm_inv, norm_inv, hx, hy]
  simpa using h.2

omit [IsUltrametricDist K] in
private theorem adjoint_charpoly_coeff_close {u u' : K} (h : ‖u - u'‖ < 1) (i : ℕ) :
    ‖(a0F u).coeff i - (a0F u').coeff i‖ < 1 := by
  simp only [a0F, coeff_add, coeff_C_mul, coeff_X_pow]
  rcases i with _ | _ | _ | _ | i
  · simp
  · simpa using h
  · rw [norm_sub_rev] at h
    simpa [neg_add_eq_sub] using h
  · simp
  · simp

end Rel

private theorem adjoint_square_apply {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (s : Γ) :
    (ad0 ρ s : Matrix (Fin 3) (Fin 3) k) =
      ((ρ s : Matrix (Fin 2) (Fin 2) k).det)⁻¹ • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k) := by
  rw [ad0, tw_val]
  simp

private theorem adjoint_square_conjugate {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (g : GL (Fin 2) k) (s : Γ) :
    ((Units.map (symSquareMatrixHom k) g * ad0 ρ s * (Units.map (symSquareMatrixHom k) g)⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det)⁻¹ •
        symSquareMatrixHom k ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, adjoint_square_apply, Units.val_mul, Units.val_mul, Matrix.det_units_conj, map_mul, map_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  rfl

private theorem symmetric_square_preserves_form (S : Type) [CommRing S] (g : Matrix (Fin 2) (Fin 2) S) :
    (symSquareMatrixHom S g)ᵀ * !![0, 0, -2; 0, 1, 0; -2, 0, 0] * symSquareMatrixHom S g =
      g.det ^ 2 • !![0, 0, -2; 0, 1, 0; -2, 0, 0] := by
  rw [Matrix.det_fin_two]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> ring

private theorem continuous_symmetric_square (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] : Continuous (symSquareMatrixHom S) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> fun_prop

private theorem symmetric_square_diagonal (S : Type) [CommRing S] (d : Fin 2 → S) :
    symSquareMatrixHom S (Matrix.diagonal d) = Matrix.diagonal ![d 0 ^ 2, d 0 * d 1, d 1 ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom]

private theorem symmetric_square_upper_triangular (S : Type) [CommRing S] (m : Matrix (Fin 2) (Fin 2) S) (h : m 1 0 = 0) :
    (∀ i j, j < i → symSquareMatrixHom S m i j = 0) ∧
      ∀ i, symSquareMatrixHom S m i i = ![m 0 0 ^ 2, m 0 0 * m 1 1, m 1 1 ^ 2] i := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [symSquareMatrixHom, h]
  · intro i
    fin_cases i <;> simp [symSquareMatrixHom, h]

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.ad0Facts :
    UpperTheory.V.Sd.Ad0Facts := by
  intro l _ Γ _ _ ρ
  have hd0 : ∀ g : GL (Fin 2) (Qbar l), (g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ≠ 0 := fun g => g.det_ne_zero
  have hcp : ∀ s, (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly =
      a0F (((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det)⁻¹ * (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace ^ 2 - 1) := fun s => by
    rw [adjoint_square_apply, adjoint_square_charpoly _ _ _ (inv_mul_cancel₀ (hd0 _))]
  refine ⟨fun h => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hA : Continuous fun g : GL (Fin 2) (Qbar l) =>
        ((g : Matrix (Fin 2) (Fin 2) (Qbar l)).det)⁻¹ • symSquareMatrixHom (Qbar l) (g : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
      (Units.continuous_val.matrix_det.inv₀ hd0).smul ((continuous_symmetric_square _).comp Units.continuous_val)
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (hA.comp h).congr fun s => (adjoint_square_apply ρ s).symm
    · refine (hA.comp h.inv).congr fun s => ?_
      rw [← map_inv, adjoint_square_apply, map_inv]
      rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 0, -2; 0, 1, 0; -2, 0, 0] (by simp [Matrix.det_fin_three]), ?_, fun s => ?_⟩
    · change (!![0, 0, -2; 0, 1, 0; -2, 0, 0] : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ = !![0, 0, -2; 0, 1, 0; -2, 0, 0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · change _ * (!![0, 0, -2; 0, 1, 0; -2, 0, 0] : Matrix (Fin 3) (Fin 3) (Qbar l)) * _ = !![0, 0, -2; 0, 1, 0; -2, 0, 0]
      rw [adjoint_square_apply, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, symmetric_square_preserves_form, smul_smul, smul_smul,
        ← pow_two, ← mul_pow, inv_mul_cancel₀ (hd0 _), one_pow, one_smul]
  · rintro H a b ⟨g, hg⟩
    refine (shapeFacts l Γ 3 (ad0 ρ) 1).2.1 H ![a / b, 1, b / a] _ Fin.revPerm ⟨Units.map (symSquareMatrixHom _) g, fun s hs => ?_⟩ ?_
    · rw [adjoint_square_conjugate, hg s hs, symmetric_square_diagonal, ← Matrix.diagonal_smul, Matrix.det_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp <;> field_simp
    · intro i s _
      fin_cases i <;> rfl
  · rintro H κ ⟨g, hg⟩
    refine ⟨Units.map (symSquareMatrixHom _) g, fun s => ?_⟩
    obtain ⟨h1, h2⟩ := hg s
    obtain ⟨k1, k2⟩ := symmetric_square_upper_triangular _ _ (h1 1 0 (by decide))
    rw [adjoint_square_conjugate]
    refine ⟨fun i j hij => by rw [Matrix.smul_apply, k1 i j hij, smul_zero], fun i => ?_⟩
    rw [Matrix.smul_apply, k2, Matrix.det_fin_two, h2 0, h2 1, h1 1 0 (by decide)]
    fin_cases i <;> simp <;> field_simp
  · intro s a b h
    obtain ⟨h1, h0⟩ := quadratic_charpoly_coeff_difference (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) a b
    rw [h, sub_self] at h1 h0
    rw [hcp, sub_eq_zero.mp (neg_eq_zero.mp h1.symm), sub_eq_zero.mp h0.symm, adjoint_charpoly_roots _ _ a.ne_zero b.ne_zero]
    simp
  · intro a b hab h s i
    obtain ⟨h1, h0⟩ := quadratic_charpoly_coeff_difference (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) (a s) (b s)
    have k1 := h s 1
    have k0 := h s 0
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at k1 k0
    rw [h1, norm_neg] at k1
    rw [h0] at k0
    have ht : Rl (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace ((a s : Qbar l) + b s) :=
      ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hab s).1.le (hab s).2.le), k1⟩
    have hn : ‖(a s : Qbar l) * b s‖ = 1 := by rw [norm_mul, (hab s).1, (hab s).2, one_mul]
    have hd : Rl (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det ((a s : Qbar l) * b s) := ⟨hn.le, k0⟩
    have e := ((hd.inv hn).mul (ht.mul ht)).2
    rw [← pow_two, ← pow_two, ← sub_sub_sub_cancel_right _ _ 1] at e
    have := adjoint_charpoly_coeff_close e i
    rw [adjoint_charpoly_roots _ _ (a s).ne_zero (b s).ne_zero] at this
    rw [hcp]
    rw [Fin.prod_univ_three, mul_right_comm, mul_comm (X - C _) (X - C _), mul_right_comm]
    simpa using this
end

section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

private theorem irr_of_le {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) {H H' : Subgroup Γ}
    (h : H ≤ H') (hi : IsIrr (ρ.comp H.subtype)) : IsIrr (ρ.comp H'.subtype) := by
  exact ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => hi.2.2 W hW fun g v hv => hI ⟨g, h g.2⟩ v hv⟩

private theorem norm_one_of_fin {l : ℕ} [Fact l.Prime] (a : (Qbar l)ˣ) (ha : IsOfFinOrder a) : ‖(a : Qbar l)‖ = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  have h1 : ‖(a : Qbar l)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

private theorem norm_cyc (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : G F Ω) :
    ‖(cycBar F Ω l s : Qbar l)‖ = 1 := by
  have h : (cycBar F Ω l s : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl
  rw [h, norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
  exact PadicInt.norm_units _

theorem UpperTheory.V.Sd.sI :
    UpperTheory.V.Sd.SI := by
  intro l _ hl Ω _ _ _ ι φ θ k hk hφ ρ hρ
  have hn : ∀ s, ‖(((cycBar ℚ Ω l ^ (k - 1) * φ) s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    intro s
    have h1 : IsOfFinOrder (φ s) := by
      obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hφ
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]⟩
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow,
      norm_cyc, norm_one_of_fin _ h1, one_pow, one_mul]
  have key : ∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) → H.Normal → ¬ IsIrr (ρ.comp H.subtype) →
      (∀ s ∈ H, Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s) 1) ∧ ∀ s, Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s ^ 2) 1 := by
    intro H hH hN hI
    refine sIabs l hl _ ρ _ hn hρ.irr hρ.res H hN ?_ hI
    obtain ⟨s, hs, a, ha, hc⟩ := eisReg l Ω ι φ θ k hk ρ hρ H hH
    refine ⟨s, hs, ?_⟩
    have ha1 : (a : Qbar l) ≠ 1 := by
      intro h
      have : a = 1 := Units.ext h
      exact ha (this ▸ IsOfFinOrder.one)
    rw [hc]
    exact separable_X_sub_C.mul separable_X_sub_C
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 ha1).isUnit)
  refine ⟨fun H hH hN ⟨s, hs, hc⟩ => ?_, fun ⟨s, hc⟩ H hH => ?_⟩
  · by_contra hI
    exact hc ((key H hH hN hI).1 s hs)
  · haveI : IsGalois ℚ Ω := ⟨⟩
    haveI : Finite (G ℚ Ω ⧸ H) := H.quotient_finite_of_isOpen hH
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hO : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
    refine irr_of_le ρ H.normalCore_le ?_
    by_contra hI
    exact hc ((key _ hO inferInstance hI).2 s)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Sd

end UpperTheory.V.Sd

open UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holLin :
    UpperTheory.V.Sd.HolLin :=
  _root_.UpperTheory.Reformulated.B.Gr32.holLin
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section CongLemmas

variable {l : ℕ} [Fact l.Prime]

private theorem cong_trans {a b c : (Qbar l)ˣ} (h : Cong a b) (h' : Cong b c) : Cong a c := by
  unfold Cong at *
  have := IsUltrametricDist.norm_add_le_max ((a : Qbar l) - b) ((b : Qbar l) - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt h h')

private theorem cong_norm {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  unfold Cong at h
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -(b : Qbar l))
    (by rw [← sub_eq_add_neg, norm_neg, hb]; exact h.trans_le (le_max_right _ _))
  rw [this, norm_neg, hb]

private theorem cong_mul_right {a b : (Qbar l)ˣ} (h : Cong a b) (c : (Qbar l)ˣ) (hc : ‖(c : Qbar l)‖ = 1) :
    Cong (a * c) (b * c) := by
  unfold Cong at *
  rw [Units.val_mul, Units.val_mul, ← sub_mul, norm_mul, hc, mul_one]
  exact h

private theorem cong_mul {a b c d : (Qbar l)ˣ} (h : Cong a b) (h' : Cong c d) (hb : ‖(b : Qbar l)‖ = 1)
    (hd : ‖(d : Qbar l)‖ = 1) : Cong (a * c) (b * d) := by
  refine cong_trans (cong_mul_right h c (cong_norm h' hd)) ?_
  rw [mul_comm b c, mul_comm b d]
  exact cong_mul_right h' b hb

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

private theorem cyc_val (s : _root_.Formalism.ConjugateSelfDual.G F Ω) :
    ((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl

end CongLemmas

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Gal

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem cyc_ine [IsAlgClosure F Ω] {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) {s : _root_.Formalism.ConjugateSelfDual.G F Ω}
    (hs : s ∈ Ine (F := F) A) : cycBar F Ω l s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have h' : ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    have hln : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
      have h2 : A.valuation (l : Ω) = 1 :=
        le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hA)
      rw [Nat.cast_pow, Valuation.map_pow, h2, one_pow]
      exact lt_irrefl 1
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    set c := PadicInt.toZModPow n ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) with hc
    have hσζ : s ζ = ζ ^ c.val := cyclotomicCharacter.spec (L := Ω) l
      (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω s) ζ hζ.pow_eq_one
    have hlt := hs.2 ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le
    rw [hσζ] at hlt
    have heq : ζ ^ c.val = ζ := by
      refine ReciprocityTheory.Gal.eq_of_pow_eq_one A hln ?_ hζ.pow_eq_one hlt
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have heq' : (hζ.isUnit hN0).unit ^ c.val = (hζ.isUnit hN0).unit ^ 1 :=
      Units.ext (by simpa using heq)
    have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
    rw [map_natCast, ← ZMod.natCast_zmod_val c]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'
  apply Units.ext
  rw [cyc_val, h']; simp

private theorem ordAt_tw {n : ℕ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ : Fin n → _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ}
    {A : ValuationSubring Ω} (h : OrdAt r m ψ A) (δ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) (hn : ∀ s, ‖(δ s : Qbar l)‖ = 1) (a : ℤ)
    (hδ : ∀ s ∈ Ine (F := F) A, δ s = cycBar F Ω l s ^ a) :
    OrdAt (tw r δ) (fun i => m i + a) (fun i => ψ i * δ) A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  refine ⟨_, (shapeFacts l _ n r δ).2.2.1 _ κ h1, fun i s hs => ?_, fun i s => cong_mul_right (h3 i s) _ (hn _)⟩
  rw [zpow_add, ← h2 i s hs, ← hδ s hs]; rfl

end Shape

section Up

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Up

end UpperTheory.V.Sd
end
end
