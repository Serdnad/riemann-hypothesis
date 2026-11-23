module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle002
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem conj_entry_int {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} {ha : 0 < a₀} {hdK : 0 < dK} {lam : ℂ} {hlam : lam ≠ 0}
    (hCm : CmOK a₀ b₀ c₀ dK) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) {n : Type} [Fintype n] [DecidableEq n]
    (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (hΛ : IsSelfDual (matH h) Λ)
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hIdx : ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)))
    (τ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (hτ : ∀ y ∈ pow4 Λ, τ y ∈ pow4 Λ) (x w : Fin 4 × n) :
    ∃ q₁ q₂ : ℚ, padicNorm l q₁ ≤ 1 ∧ padicNorm l q₂ ≤ 1 ∧
      g₁ (τ (g₁.symm (Pi.single w 1))) x = q₁ + q₂ * sq dK := by
  classical
  have hl2 : ¬ l ∣ 2 := fun h2 => by have := Nat.le_of_dvd two_pos h2; omega
  have hla : ¬ l ∣ a₀ := by
    intro hla
    apply hin
    refine ⟨(b₀ : ZMod l), ?_⟩
    have e := congrArg (Int.cast : ℤ → ZMod l) hCm.1
    push_cast at e
    have ha0 : (a₀ : ZMod l) = 0 := (CharP.cast_eq_zero_iff (ZMod l) l a₀).mpr hla
    rw [ha0] at e
    linear_combination -e
  set N := relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) with hN
  have hN0 : N ≠ 0 := fun h0 => hIdx (by rw [h0]; exact dvd_zero l)
  have hden : ¬ l ∣ 2 * N ^ 2 * a₀ := by
    intro hd
    have hp : l.Prime := Fact.out
    rcases (Nat.Prime.dvd_mul hp).mp hd with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · exact hl2 h''
      · exact hIdx (hp.dvd_of_dvd_pow h'')
    · exact hla h'
  have he : Pi.single w (lam * (a₀ : ℂ)) ∈ stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n) := by
    intro i _
    by_cases hi : i = w
    · subst hi
      rw [Pi.single_eq_same]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).ω₁_mem_lattice
    · rw [Pi.single_eq_of_ne hi]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).lattice.toAddSubgroup.zero_mem
  have h1 := idx_smul_symm_mem (cmL a₀ b₀ dK ha hdK lam hlam) h Λ hΛ g₁ hIso he
  have h3 := idx_smul_mem (cmL a₀ b₀ dK ha hdK lam hlam) Λ g₁ (hτ _ h1)
  have h4 := h3 x (Set.mem_univ x)
  obtain ⟨m, k, hmk⟩ := PeriodPair.mem_lattice.mp h4
  have hsingle : Pi.single w (lam * (a₀ : ℂ)) = (lam * (a₀ : ℂ)) • Pi.single w (1 : ℂ) := by
    ext i; by_cases hi : i = w
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  rw [hsingle, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hmk
  simp only [map_smul, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at hmk
  have hω1 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₁ = lam * (a₀ : ℂ) := rfl
  have hω2 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₂ = lam * cmTheta b₀ dK := rfl
  rw [hω1, hω2, cmTheta] at hmk
  refine ⟨((2 * m * a₀ + k * b₀ : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ),
    ((k : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ), ?_, ?_, ?_⟩
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    have hac : (a₀ : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    set E := g₁ (τ (g₁.symm (Pi.single w 1))) x with hEdef
    have hE : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) * E =
        lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) := by
      linear_combination (-2 : ℂ) * hmk
    have hc : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) ≠ 0 := by simp [hNc, hac, hlam]
    have hE' : E = lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) /
        ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) := by
      rw [eq_div_iff hc, mul_comm]; exact hE
    rw [hE']
    unfold sq
    push_cast
    field_simp

theorem gmat_eq {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    gmat g = LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
  ext x w
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem conj_matrix_apply {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (T : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (x w : Fin 4 × n) :
    (LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g) x w
      = g (Matrix.toLin' T (g.symm (Pi.single w 1))) x := by
  have e : LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g =
      LinearMap.toMatrix' ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ Matrix.toLin' T ∘ₗ
        (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', gmat_eq, mul_assoc]
  rw [e, LinearMap.toMatrix'_apply]
  rfl

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

def mv {R : Type*} [Zero R] [One R] (a : Fin 4) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = a ∧ y.1 = 0 ∧ x.2 = y.2 then 1 else 0

theorem mv_mul_apply {R : Type*} [CommRing R] (a : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((mv a : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = a then G (0, z.2) w else 0 := by
  simp only [Matrix.mul_apply, mv]
  by_cases h : z.1 = a
  · rw [Fintype.sum_eq_single (0, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

theorem blockShift_mul_apply {R : Type*} [CommRing R] (k : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((bmv0 k : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = 0 then G (k, z.2) w else 0 := by
  simp only [Matrix.mul_apply, bmv0]
  by_cases h : z.1 = 0
  · rw [Fintype.sum_eq_single (k, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

theorem mv_mulVec (a : Fin 4) (y : Fin 4 × n → ℂ) :
    (mv a : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = a then y (0, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, mv]
  by_cases h : x.1 = a
  · rw [Fintype.sum_eq_single (0, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

theorem blockShift_mulVec (k : Fin 4) (y : Fin 4 × n → ℂ) :
    (bmv0 k : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = 0 then y (k, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, bmv0]
  by_cases h : x.1 = 0
  · rw [Fintype.sum_eq_single (k, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

theorem mv_pres (Λ : AddSubgroup (n → ℂ)) (a : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (mv a : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, mv_mulVec]
  by_cases h : b = a
  · subst h
    convert hy' 0 using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

theorem blockShift_mapsTo (Λ : AddSubgroup (n → ℂ)) (k : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (bmv0 k : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, blockShift_mulVec]
  by_cases h : b = 0
  · subst h
    convert hy' k using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

theorem bd4_transpose {R : Type*} [Zero R] (P : Matrix n n R) : (bd4 P).transpose = bd4 P.transpose := by
  ext x y
  by_cases h : x.1 = y.1
  · simp [bd4, Matrix.transpose_apply, h]
  · simp [bd4, Matrix.transpose_apply, h, Ne.symm h]

theorem bd4_smul {R : Type*} [CommRing R] (c : R) (P : Matrix n n R) : bd4 (c • P) = c • bd4 P := by
  ext x y
  by_cases h : x.1 = y.1 <;> simp [bd4, h]

theorem bd4_one {R : Type*} [CommRing R] : bd4 (1 : Matrix n n R) = 1 := by
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [bd4, Matrix.one_apply, Prod.ext_iff, h1, h2]

theorem blockDiag_mul_blockShift {R : Type*} [CommRing R] (P : Matrix n n R) (k : Fin 4) :
    bd4 P * bmv0 k = bmv0 k * bd4 P := by
  ext x y
  rw [blockShift_mul_apply]
  simp only [Matrix.mul_apply, bd4, bmv0]
  rw [Fintype.sum_eq_single (0, y.2)]
  · by_cases h1 : x.1 = 0 <;> by_cases h2 : y.1 = k
    · simp [h1, h2]
    · have h2' : k ≠ y.1 := fun h => h2 h.symm
      simp [h1, h2, h2']
    · simp [h1, h2]
    · simp [h1, h2]
  · intro z hz
    by_cases hc : z.1 = 0 ∧ y.1 = k ∧ z.2 = y.2
    · exact absurd (Prod.ext hc.1 hc.2.2 : z = (0, y.2)) hz
    · rw [if_neg hc, mul_zero]

theorem exists_cols (G Gi : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (hG : G * Gi = 1) :
    ∃ w : n → Fin 4 × n, IsUnit (Matrix.of fun i j => G (0, i) (w j)) := by
  classical
  set v : Fin 4 × n → (n → ℂ) := fun j i => G (0, i) j with hv
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ j, (∑ k, Gi j (0, k) * x k) • v j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
      have h : ∀ k, ∑ j, G (0, i) j * Gi j (0, k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hG (0, i)) (0, k)
        simpa [Matrix.mul_apply, Matrix.one_apply] using this
      symm
      calc ∑ j, (∑ k, Gi j (0, k) * x k) * G (0, i) j
          = ∑ k, (∑ j, G (0, i) j * Gi j (0, k)) * x k := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
        _ = x i := by simp [h]
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range v)
  rw [hspan] at hbspan
  let B := Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
  let e := B.indexEquiv (Pi.basisFun ℂ n)
  have hmem : ∀ i : n, ∃ j, v j = ((e.symm i : b) : n → ℂ) := fun i => hbs (e.symm i).2
  choose w hw using hmem
  refine ⟨w, ?_⟩
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have hfun : (Matrix.of fun i j => G (0, i) (w j)).col =
      (fun x : b => (x : n → ℂ)) ∘ e.symm := by
    funext j i
    simp [Matrix.col, Matrix.transpose_apply, ← hw j, hv]
  rw [hfun]
  exact hbli.comp _ e.symm.injective

end Blocks

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

theorem bd4_mul_apply {R : Type*} [CommRing R] (P : Matrix n n R) (Q : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (a : Fin 4) (i : n) (w : Fin 4 × n) : (bd4 P * Q) (a, i) w = ∑ j, P i j * Q (a, j) w := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [bd4]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [bd4, Ne.symm hb]
  · simp

theorem bd4_mul {R : Type*} [CommRing R] (P Q : Matrix n n R) : bd4 P * bd4 Q = bd4 (P * Q) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [bd4_mul_apply]
  by_cases hab : a = b
  · subst hab
    simp [bd4, Matrix.mul_apply]
  · simp [bd4, hab]

theorem bd4_map {R S : Type*} [Zero R] [Zero S] (f : R → S) (hf : f 0 = 0) (P : Matrix n n R) :
    (bd4 P).map f = bd4 (P.map f) := by
  ext x y
  simp only [Matrix.map_apply, bd4]
  split_ifs
  · rfl
  · exact hf

theorem blockShift_map {R S : Type*} [Zero R] [One R] [Zero S] [One S] (f : R → S) (hf : f 0 = 0) (hf1 : f 1 = 1)
    (k : Fin 4) : (bmv0 (n := n) k : Matrix _ _ R).map f = bmv0 k := by
  ext x y
  simp only [Matrix.map_apply, bmv0]
  split_ifs
  · exact hf1
  · exact hf

end Blocks

theorem sq_sq (d : ℕ) : sq d ^ 2 = -(d : ℂ) := by
  show (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ)
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  ring

theorem lmat_coe {l : ℕ} [Fact l.Prime] {m m' : Type} (d : ℕ) (ι : ℂ ≃+* ℂ_[l]) (δ : MaximalUnramifiedExtension l)
    (hδ : (δ : ℂ_[l]) = ι (sq d)) (A B : Matrix m m' ℚ) :
    (lmat δ A B).map (MaximalUnramifiedExtension l).subtype = (kmat d A B).map ι := by
  ext x y
  simp only [lmat, kmat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, map_ratCast, hδ]
  simp
  exact Or.inl hδ

theorem hermFrame_of (hF : FrobStep) (hR : RatStep) (hL : LocCore) : Formalism.L2.Th1.Top.FrP.HermFrame := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm l _ hl hldK hsq ι σ hσ n _ _ h Λ g₀ g₁ hlat hiso hidx
  obtain ⟨P₀, M₁, M₂, R₁, R₂, c, hc, hg, hRR, hU⟩ :=
    hR a₀ b₀ c₀ dK ha hdK lam hlam hcm l hl hldK hsq n h Λ g₀ g₁ hlat hiso hidx
  obtain ⟨hnorm, δ, hδ, hσδ⟩ := hF l dK hl hldK hcm.2.2.2 hcm.2.2.1 hsq ι σ hσ
  have hδ2 : δ ^ 2 = -(dK : MaximalUnramifiedExtension l) := by
    apply Subtype.ext
    have e1 : ((δ ^ 2 : MaximalUnramifiedExtension l) : ℂ_[l]) = (δ : ℂ_[l]) ^ 2 := rfl
    have e2 : ((-(dK : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l]) = -(dK : ℂ_[l]) := by simp
    rw [e1, e2, hδ, ← map_pow, sq_sq, map_neg, map_natCast]
  have hmulι : ∀ {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ),
      (A * B).map ι = A.map ι * B.map ι := by
    intro p q r _ A B
    have : (A * B).map (ι : ℂ →+* ℂ_[l]) = A.map (ι : ℂ →+* ℂ_[l]) * B.map (ι : ℂ →+* ℂ_[l]) :=
      Matrix.map_mul
    simpa using this
  have hinj : ∀ {p q : Type}, Function.Injective
      (fun A : Matrix p q (MaximalUnramifiedExtension l) => A.map (MaximalUnramifiedExtension l).subtype) :=
    fun {p q} => Matrix.map_injective Subtype.val_injective
  have hLeq : (lmat δ M₁ M₂).transpose * bd4 (lmat δ R₁ R₂) * lmat δ M₁ (-M₂) =
      (c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) := by
    apply hinj
    have h1 := congrArg (fun A => A.map ι) hRR
    simp only [hmulι, Matrix.transpose_map, bd4_map ι (map_zero ι)] at h1
    simp only [Matrix.map_mul, Matrix.transpose_map, bd4_map (MaximalUnramifiedExtension l).subtype (map_zero _),
      lmat_coe dK ι δ hδ]
    rw [h1]
    ext x y
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [map_ratCast]
  have hUk : ∀ k : Fin 4, ∃ U₁ U₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ,
      (∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) ∧
      bmv0 k * lmat δ M₁ M₂ = lmat δ M₁ M₂ * lmat δ U₁ U₂ := by
    intro k
    obtain ⟨U₁, U₂, hUn, hUe⟩ := hU k
    refine ⟨U₁, U₂, hUn, ?_⟩
    apply hinj
    have h1 := congrArg (fun A => A.map ι) hUe
    simp only [hmulι, blockShift_map ι (map_zero ι) (map_one ι)] at h1
    simp only [Matrix.map_mul, blockShift_map (MaximalUnramifiedExtension l).subtype (map_zero _) (map_one _),
      lmat_coe dK ι δ hδ]
    exact h1
  obtain ⟨T, Ti, hTTi, hUn⟩ := hL l dK σ δ hl hldK hsq hnorm hδ2 hσδ n M₁ M₂ R₁ R₂ c hc hLeq hUk
  refine ⟨bd4 Ti * lmat δ M₁ M₂, ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype), hUn, ?_⟩
  intro i' i w
  have hγ : (bd4 Ti * lmat δ M₁ M₂).map (MaximalUnramifiedExtension l).subtype =
      bd4 (Ti.map (MaximalUnramifiedExtension l).subtype) * (kmat dK M₁ M₂).map ι := by
    rw [Matrix.map_mul, bd4_map (MaximalUnramifiedExtension l).subtype (map_zero _), lmat_coe dK ι δ hδ]
  have hTT : T.map (MaximalUnramifiedExtension l).subtype * Ti.map (MaximalUnramifiedExtension l).subtype = 1 := by
    rw [← Matrix.map_mul, hTTi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hB : bd4 (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) * bd4 (Ti.map (MaximalUnramifiedExtension l).subtype) =
      bd4 (ι lam⁻¹ • P₀.map ι) := by
    rw [bd4_mul, Matrix.smul_mul, Matrix.mul_assoc, hTT, Matrix.mul_one]
  have hsm : ∀ (x : ℂ_[l]) (Q : Matrix n n ℂ_[l]), bd4 (x • Q) = x • bd4 Q := by
    intro x Q
    ext p q
    simp only [bd4, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hG : (gmat g₁).map ι = bd4 (ι lam⁻¹ • P₀.map ι) * (kmat dK M₁ M₂).map ι := by
    rw [hg, hsm, Matrix.smul_mul, ← bd4_map ι (map_zero ι), ← hmulι]
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  calc ∑ j, (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) i j *
        (((bd4 Ti * lmat δ M₁ M₂) (i', j) w : MaximalUnramifiedExtension l) : ℂ_[l])
      = (bd4 (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) *
          (bd4 Ti * lmat δ M₁ M₂).map (MaximalUnramifiedExtension l).subtype) (i', i) w := by
        rw [bd4_mul_apply]
        rfl
    _ = (gmat g₁).map ι (i', i) w := by
        rw [hγ, ← Matrix.mul_assoc, hB, hG]
    _ = ι (g₁.symm (Pi.single w 1) (i', i)) := rfl

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end
