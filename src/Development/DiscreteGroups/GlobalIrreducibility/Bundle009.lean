module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle005
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle006
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle007
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
public import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {G : Type} [Group G] [Fintype G]

theorem simple_of_isIrr (τ : FDRep ℂ G) (h : GlobalTheory.GLq.IsIrr τ.character) : Simple τ := by
  obtain ⟨V, hV, hch⟩ := h
  rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
  simpa only [hch] using hV

end DiscreteGroups.sglob.DzType.Kon
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ} {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem agree_of_entry_one (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  set r : Fin (m + 1) → k := fun j => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
    Matrix.of fun i j => if i = 0 then r j else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j
  have hMtri : ∀ i j : Fin (m + 1), j < i → M i j = 0 := by
    intro i j hij
    have hi : i ≠ 0 := fun e => by subst e; exact (Fin.not_lt_zero j) hij
    simp [M, hi, Matrix.one_apply_ne hij.ne']
  have hMdiag : ∀ i, M i i = 1 := by
    intro i
    by_cases hi : i = 0
    · subst hi; simpa [M, r] using hg
    · simp [M, hi]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hMtri i j hij)]
    simp [hMdiag]
  set n : GL (Fin (m + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  have hnv : (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = M := rfl
  have hn : n ∈ unipB k (Fin (m + 1)) := (mem_unipB k).2 ⟨fun i j hij => by rw [hnv]; exact hMtri i j hij,
    fun i => by rw [hnv]; exact hMdiag i⟩
  have hwn : ∀ b, ((longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
      (Fin.last m) b = r b := by
    intro b
    rw [hnv, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (m + 1))]
    · rw [longElt_last, if_pos rfl, one_mul]
      simp [M, r]
    · intro a _ ha
      rw [longElt_last, if_neg ha, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set p : GL (Fin (m + 1)) k := longElt (m + 1) k * n * g
  have hP : IsP p := by
    intro j
    show ((longElt (m + 1) k * n * g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = _
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply]
    calc _ = ∑ b, r b * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) b j :=
          Finset.sum_congr rfl fun b _ => by rw [hwn b]
      _ = _ := by
        simp only [r]
        rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : g = n⁻¹ * (longElt (m + 1) k)⁻¹ * p := by
    simp only [p, mul_assoc, inv_mul_cancel_left]
  rw [hg', longElt_inv]
  simp only [map_mul, Module.End.mul_apply]
  rw [hl₁ _ (inv_mem hn), hl₂ _ (inv_mem hn), hW _ _ (agree_translate hl₁ hl₂ hX hP)]

theorem val_scalar (z : kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      Matrix.diagonal fun _ => (z : k) := by
  first
  | rfl
  | (ext i j; simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply])

theorem agree_scalar {ω₁ ω₂ : kˣ →* ℂˣ} (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂)
    (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) (u : kˣ)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = u) :
    (ω₁ u : ℂ) * l₁ (π₁ g v₁) = (ω₂ u : ℂ) * l₂ (π₂ g v₂) := by
  have hent : (((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u * g)⁻¹ : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1 := by
    rw [mul_inv_rev, ← map_inv, Units.val_mul, val_scalar, Matrix.mul_diagonal, hg, Units.mul_inv]
  have := agree_of_entry_one hl₁ hl₂ hW hX _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₁, h₂, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at this

end DiscreteGroups.sglob.LConv

end
end

section

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConvKir

theorem sum_char_eq_zero {A : Type} [AddCommGroup A] (L L'' : AddSubgroup A)
    [Fintype (L ⧸ L''.addSubgroupOf L)] (χ : A → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y)
    (h'' : ∀ x ∈ L'', χ x = 1) (x₀ : L) (hne : χ x₀ ≠ 1) :
    ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
  have hterm : ∀ q : L ⧸ L''.addSubgroupOf L,
      χ ((Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) : L) : A) = χ x₀ * χ ((Quotient.out q : L) : A) := by
    intro q
    set z := Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) with hz
    have hq : ((z : L) : L ⧸ L''.addSubgroupOf L) = ((x₀ + Quotient.out q : L) : L ⧸ L''.addSubgroupOf L) := by
      rw [hz, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    have hd := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hq)
    have e : (x₀ : A) + ((Quotient.out q : L) : A) = (z : A) + ((-z + (x₀ + Quotient.out q) : L) : A) := by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
    rw [← hχ, e, hχ, h'' _ hd, mul_one]
  have hT := Equiv.sum_comp (Equiv.addLeft ((x₀ : L ⧸ L''.addSubgroupOf L))) (fun q => χ ((Quotient.out q : L) : A))
  simp only [Equiv.coe_addLeft, hterm, ← Finset.mul_sum] at hT
  have h0 : (χ x₀ - 1) * ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
    rw [sub_mul, hT, one_mul, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

variable {k : Type} [Field k]

theorem psi_neg_mul (ψ : AddChar k Circle) (t : k) : ((ψ (-t) : Circle) : ℂ) * (ψ t : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem l_gU {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (l : Module.Dual ℂ V) (hl : IsFunctional ψ ρ l)
    (j : ℕ) (hj : j + 1 < m + 1) (g : GL (Fin (m + 1)) k) (hg : InH (j + 1) g) (x : Fin (m + 1) → k) (w : V) :
    l (ρ g (ρ (U ⟨j + 1, hj⟩ x) w)) =
      (ψ (∑ r, (if r < (⟨j + 1, hj⟩ : Fin (m + 1)) then
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, by omega⟩ r else 0) * x r) : ℂ) * l (ρ g w) := by
  rw [← Module.End.mul_apply, ← map_mul, conj_U j hj g hg x, map_mul, Module.End.mul_apply,
    hl _ (U_mem _ _), superDiag_U]

end DiscreteGroups.sglob.LConvKir
end
end
