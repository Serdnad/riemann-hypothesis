module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle005
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ}

def cornerHom : GL (Fin m) k →* GL (Fin (m + 1)) k :=
  (emb₂ k (stdSum (rfl : m + 1 = m + 1))).comp (MonoidHom.inl _ _)

theorem cornerHom_apply (g : GL (Fin m) k) : cornerHom g = corner g := rfl

def IsP (p : GL (Fin (m + 1)) k) : Prop :=
  ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j

theorem mul_apply_last_of_isMirabolic {a b : GL (Fin (m + 1)) k} (ha : IsP a) (j : Fin (m + 1)) :
    ((a * b : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  rw [Units.val_mul, Matrix.mul_apply]
  calc ∑ c, (a : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j
      = ∑ c, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j :=
        Finset.sum_congr rfl fun c _ => by rw [ha c]
    _ = _ := by rw [← Matrix.mul_apply, Matrix.one_mul]

theorem isMirabolic_mul {a b : GL (Fin (m + 1)) k} (ha : IsP a) (hb : IsP b) : IsP (a * b) := fun j =>
  (mul_apply_last_of_isMirabolic ha j).trans (hb j)

theorem isMirabolic_corner (g : GL (Fin m) k) : IsP (corner g) := corner_last g

theorem exists_eq_mul_corner {p : GL (Fin (m + 1)) k} (hp : IsP p) :
    ∃ u ∈ unipB k (Fin (m + 1)), ∃ h : GL (Fin m) k, p = u * corner h := by
  have hne : ∀ j : Fin m, Fin.last m ≠ j.castSucc := fun j => (Fin.castSucc_lt_last j).ne'
  set A : Matrix (Fin m) (Fin m) k := (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).submatrix Fin.castSucc Fin.castSucc
  have he : ((-1 : k) ^ (m + m)) = 1 := by rw [← two_mul, pow_mul]; simp
  have hdet : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).det = A.det := by
    have hp' : ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := hp
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    simp [hp', Matrix.one_apply, hne, Fin.succAbove_last, A, he]
  have hA : A.det ≠ 0 := by
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero
  set h : GL (Fin m) k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
  have hh : (h : Matrix (Fin m) (Fin m) k) = A := rfl
  refine ⟨p * corner h⁻¹, ?_, h, ?_⟩
  swap
  · rw [mul_assoc, ← cornerHom_apply, ← cornerHom_apply, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hL : ∀ j, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := fun j =>
    (mul_apply_last_of_isMirabolic hp j).trans (corner_last _ j)
  have hB : ∀ i j : Fin m, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      i.castSucc j.castSucc = (1 : Matrix (Fin m) (Fin m) k) i j := by
    intro i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, corner_last, Matrix.one_apply_ne (hne j)]
    simp only [corner_cs_cs, mul_zero, add_zero]
    rw [← h.mul_inv, Matrix.mul_apply, hh]
    rfl
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_ne hij.ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
      | cast j =>
        rw [hB, Matrix.one_apply_ne]
        intro e; subst e; exact lt_irrefl _ hij
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_eq]
    | cast i => rw [hB, Matrix.one_apply_eq]

section Agree

variable {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁} {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂}
  {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem agree_of_isP (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) : l₁ (π₁ p v₁) = l₂ (π₂ p v₂) := by
  obtain ⟨u, hu, h, rfl⟩ := exists_eq_mul_corner hp
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl₁ u hu, hl₂ u hu, hX h]

theorem agree_translate (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) (g : GL (Fin m) k) : l₁ (π₁ (corner g) (π₁ p v₁)) = l₂ (π₂ (corner g) (π₂ p v₂)) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  exact agree_of_isP hl₁ hl₂ hX (isMirabolic_mul (isMirabolic_corner g) hp)

end Agree

end DiscreteGroups.sglob.LConv

end
end

section

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

theorem U_zero (c : Fin (m + 1)) : U c (0 : Fin (m + 1) → k) = 1 := Units.ext (colM_zero c)

theorem conj_U (j : ℕ) (hj : j + 1 < m + 1) (g : GL (Fin (m + 1)) k) (hg : InH (j + 1) g)
    (x : Fin (m + 1) → k) :
    g * U ⟨j + 1, hj⟩ x = U ⟨j + 1, hj⟩ (fun p => ∑ r, (if r < (⟨j + 1, hj⟩ : Fin (m + 1)) then
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p r else 0) * x r) * g := by
  set c : Fin (m + 1) := ⟨j + 1, hj⟩ with hc
  have hrow : ∀ q, (g : Matrix _ _ k) c q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c q :=
    fun q => hg c q (fun h => lt_irrefl _ h.1)
  have hlow : ∀ p r : Fin (m + 1), ¬ p < c → r < c → (g : Matrix _ _ k) p r = 0 := fun p r hp hr => by
    rw [hg p r (fun h => hp (by rw [Fin.lt_def]; exact h.1)),
      Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hr))]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show (g : Matrix _ _ k) * colM c x = colM c _ * (g : Matrix _ _ k)
  ext p q
  simp only [colM, mul_add, add_mul, mul_one, one_mul, Matrix.add_apply]
  congr 1
  simp only [Matrix.mul_apply, Matrix.of_apply]
  conv_rhs => rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ c) h)]
  by_cases hq : q = c
  · rw [hq, hrow c, Matrix.one_apply_eq, mul_one]
    by_cases hp : p < c
    · rw [if_pos ⟨rfl, hp⟩]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : r < c
      · rw [if_pos ⟨rfl, hr⟩, if_pos hr]
      · rw [if_neg (fun h => hr h.2), if_neg hr]; simp
    · rw [if_neg (fun h => hp h.2)]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r < c
      · rw [hlow p r hp hr, zero_mul]
      · rw [if_neg (fun h => hr h.2), mul_zero]
  · rw [hrow q, Matrix.one_apply_ne (Ne.symm hq), mul_zero]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg (fun h => hq h.1), mul_zero]

theorem decomp (j : ℕ) (hj : j < m + 1) (M : GL (Fin (m + 1)) k) (hM : InH (j + 1) M)
    (hrow : ∀ q, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, hj⟩ q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, hj⟩ q) :
    ∃ y h, InH j h ∧ M = U ⟨j, hj⟩ y * h := by
  set jj : Fin (m + 1) := ⟨j, hj⟩ with hjj
  let y : Fin (m + 1) → k := fun p => (M : Matrix _ _ k) p jj
  refine ⟨y, U jj (-y) * M, ?_, ?_⟩
  · intro p q hpq
    show (colM jj (-y) * (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q = _
    rw [colM, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single jj (fun r _ hr => by simp [hr]) (fun h => absurd (Finset.mem_univ jj) h)]
    rw [hrow q]
    by_cases hqj : q = jj
    · rw [hqj, Matrix.one_apply_eq, mul_one]
      by_cases hp : p < jj
      · rw [if_pos ⟨rfl, hp⟩, Matrix.one_apply_ne (ne_of_lt hp)]
        simp only [y, Pi.neg_apply]; ring
      · rw [if_neg (fun h => hp h.2), add_zero]
        by_cases hpe : p = jj
        · rw [hpe]; exact hrow jj
        · refine hM p jj (fun h => hp ?_)
          rw [Fin.lt_def]; rw [Fin.ext_iff] at hpe; simp [hjj] at h hpe ⊢; omega
    · rw [Matrix.one_apply_ne (fun h => hqj h.symm), mul_zero, add_zero]
      by_cases hpe : p = jj
      · rw [hpe]; exact hrow q
      · refine hM p q (fun h => hpq ⟨?_, ?_⟩)
        · rw [Fin.ext_iff] at hpe; simp [hjj] at hpe; omega
        · rw [Fin.ext_iff] at hqj; simp [hjj] at hqj; omega
  · rw [← mul_assoc, ← U_add, add_neg_cancel, U_zero, one_mul]

theorem InH_corner (g : GL (Fin m) k) : InH m (corner g) := by
  intro p q hpq
  rw [corner, val_emb₂, Matrix.reindex_apply, Matrix.submatrix_apply]
  induction p using Fin.addCases with
  | left a =>
    induction q using Fin.addCases with
    | left b => exact absurd ⟨by simp, by simp⟩ hpq
    | right b => simp [stdSum, Matrix.one_apply, Fin.ext_iff]; omega
  | right a =>
    induction q using Fin.addCases with
    | left b => simp [stdSum, Matrix.one_apply, Fin.ext_iff]; omega
    | right b =>
      have := Subsingleton.elim a b
      subst this
      simp [stdSum]

end DiscreteGroups.sglob.LConvKir
end
end
