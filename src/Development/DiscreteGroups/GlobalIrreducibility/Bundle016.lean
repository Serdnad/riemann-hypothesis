module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle015
import Development.DiscreteGroups.GlobalIrreducibility.Bundle013
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle001
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

section Irr

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem irr_mem [ρ.IsIrreducible] (S : Submodule ℂ V) (hS : ∀ g, ∀ ⦃x⦄, x ∈ S → ρ g x ∈ S) {v : V} (hv0 : v ≠ 0)
    (hv : v ∈ S) (w : V) : w ∈ S := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation ρ) with h | h
  · exfalso
    apply hv0
    have : v ∈ (⟨S, hS⟩ : Subrepresentation ρ) := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : w ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at this
    exact this

theorem eq_zero_of_forall [ρ.IsIrreducible] (l : Module.Dual ℂ V) {v₀ : V} (hv₀ : l v₀ ≠ 0) {b : V}
    (hb : ∀ g, l (ρ g b) = 0) : b = 0 := by
  by_contra hb0
  let S : Submodule ℂ V :=
    { carrier := {x | ∀ g, l (ρ g x) = 0}
      add_mem' := fun {x y} hx hy g => by rw [map_add (f := _), map_add (f := _), hx g, hy g, add_zero]
      zero_mem' := fun g => by rw [map_zero, map_zero]
      smul_mem' := fun c x hx g => by rw [map_smul, map_smul, hx g, smul_zero] }
  have hS : ∀ h, ∀ ⦃x⦄, x ∈ S → ρ h x ∈ S := fun h x hx g => by
    rw [← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have := irr_mem S hS hb0 hb v₀ 1
  rw [map_one, Module.End.one_apply] at this
  exact hv₀ this

end Irr

theorem bigCell : BigCell := by
  intro k _ _ _ _ ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ hW ⟨v₁, v₂, hX, h0⟩
  have := π₁.irr
  have := π₂.irr
  obtain ⟨ω₁, -, h₁⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₁.smooth π₁.irr
  obtain ⟨ω₂, -, h₂⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₂.smooth π₂.irr
  obtain rfl := centralChar_eq hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hX h0
  have hall : ∀ (a : π₁.V) (b : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) a) = l₂ (π₂.ρ (corner g) b)) →
      ∀ g, l₁ (π₁.ρ g a) = l₂ (π₂.ρ g b) := fun a b hab g =>
    agree_all hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hab g
  let Y : Submodule ℂ (π₁.V × π₂.V) :=
    { carrier := {x | ∀ g, l₁ (π₁.ρ g x.1) = l₂ (π₂.ρ g x.2)}
      add_mem' := fun {x y} hx hy g => by
        rw [Prod.fst_add, Prod.snd_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx g, hy g]
      zero_mem' := fun g => by simp
      smul_mem' := fun c x hx g => by
        rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, map_smul, map_smul, hx g] }
  have hY : ∀ h (x : π₁.V × π₂.V), x ∈ Y → (π₁.ρ h x.1, π₂.ρ h x.2) ∈ Y := fun h x hx g => by
    show l₁ (π₁.ρ g (π₁.ρ h x.1)) = l₂ (π₂.ρ g (π₂.ρ h x.2))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have hv : (v₁, v₂) ∈ Y := hall v₁ v₂ hX
  have h0' : l₂ v₂ ≠ 0 := by
    have := hv 1
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
    rwa [← this]
  have hv₁ : v₁ ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hv₂ : v₂ ≠ 0 := fun e => h0' (by rw [e, map_zero])

  let f₁ : Y →ₗ[ℂ] π₁.V := (LinearMap.fst ℂ π₁.V π₂.V).comp Y.subtype
  let f₂ : Y →ₗ[ℂ] π₂.V := (LinearMap.snd ℂ π₁.V π₂.V).comp Y.subtype
  have inj₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero f₁).2 fun y hy => ?_
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := hy
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := eq_zero_of_forall (ρ := π₂.ρ) l₂ h0' fun g => by
      rw [← y.2 g, hy1, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have inj₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero f₂).2 fun y hy => ?_
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := hy
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := eq_zero_of_forall (ρ := π₁.ρ) l₁ h0 fun g => by
      rw [y.2 g, hy2, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have surj₁ : Function.Surjective f₁ := fun a => by
    have := irr_mem (ρ := π₁.ρ) (LinearMap.range f₁) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₁ ⟨⟨_, hv⟩, rfl⟩ a
    exact this
  have surj₂ : Function.Surjective f₂ := fun b => by
    have := irr_mem (ρ := π₂.ρ) (LinearMap.range f₂) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₂ ⟨⟨_, hv⟩, rfl⟩ b
    exact this
  let e₁ := LinearEquiv.ofBijective f₁ ⟨inj₁, surj₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨inj₂, surj₂⟩
  let T : π₁.V ≃ₗ[ℂ] π₂.V := e₁.symm.trans e₂
  have hT : ∀ a, (a, T a) ∈ Y := fun a => by
    have h1 : ((e₁.symm a : Y) : π₁.V × π₂.V).1 = a := e₁.apply_symm_apply a
    have := (e₁.symm a).2
    rw [← Prod.mk.eta (p := ((e₁.symm a : Y) : π₁.V × π₂.V)), h1] at this
    exact this
  have hint : ∀ g a, T (π₁.ρ g a) = π₂.ρ g (T a) := fun g a => by
    have h1 : e₁.symm (π₁.ρ g a) = ⟨_, hY g _ (hT a)⟩ := e₁.injective (by rw [e₁.apply_symm_apply]; rfl)
    show e₂ (e₁.symm (π₁.ρ g a)) = _
    rw [h1]
    rfl
  let Tint : Representation.IntertwiningMap π₁.ρ π₂.ρ :=
    { toLinearMap := T.toLinearMap
      isIntertwining' := fun g => LinearMap.ext fun a => hint g a }
  exact ⟨Tint.ofBijective T.bijective⟩

end DiscreteGroups.sglob.LConv

end
end

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem univ_supp (c : Fin n → k) : ∀ r ∉ (Finset.univ : Finset (Fin n)), c r = 0 :=
  fun r hr => absurd (Finset.mem_univ r) hr

theorem conj_S (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) :
    π x⁻¹ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add (f := _)]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ hy.good (by rw [inv_inv]; exact hx.good) ha) ?_
  refine (Submodule.span_le.2 ?_ : KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    ≤ (KUS π ψ j Finset.univ ξ).comap (π x⁻¹)) hb
  rintro _ ⟨c, -, v, rfl⟩
  refine Submodule.subset_span ⟨colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c, univ_supp _, π x⁻¹ v, ?_⟩
  rw [map_sub, map_smul, conj_apply, inv_inv, conj_colU j hj x hx hy, dotj_colMul]

theorem ne_top_of_conj (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k)
    (h : KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ ≠ ⊤) :
    KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ≠ ⊤ := by
  intro htop
  apply h
  refine eq_top_iff.2 fun v _ => ?_
  have := conj_S π ψ j hj x hx hy ξ (w := π x v) (by rw [htop]; exact Submodule.mem_top)
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

theorem KN_le (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (η : Fin n → k) (hη : ∀ c, dotj j η c = c (i0 j hj hj1)) :
    KN π ψ j ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ η := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_N j hj hj1 hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ j g = chM ψ (j + 1) n' * ((ψ (c (i0 j hj hj1)) : Circle) : ℂ) := by
    rw [chM, chM, h2, AddChar.map_add_eq_mul, Circle.coe_mul]; rfl
  have e : π g v - chM ψ j g • v = π (colU j c) (π n' v - chM ψ (j + 1) n' • v) +
      chM ψ (j + 1) n' • (π (colU j c) v - ((ψ (dotj j η c) : Circle) : ℂ) • v) := by
    rw [hη, hch, map_sub, map_smul, smul_sub, smul_smul]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩))

theorem twKer_le (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) (ξ : Fin n → k) (hz : ∀ i : Fin n, i.val < j → ξ i = 0) :
    twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, hg⟩, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_rad j hj h hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ (j + 1) n' = 1 := by rw [chM, h2, AddChar.map_zero_eq_one, Circle.coe_one]
  have hd : dotj j ξ c = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : i.val < j
    · rw [if_pos hi, hz i hi, zero_mul]
    · rw [if_neg hi]
  have e : π g v - (((1 : ↥(unipRad k (stdBlocks ![j, n - j] h)) →* ℂˣ) ⟨g, hg⟩ : ℂˣ) : ℂ) • v =
      π (colU j c) (π n' v - chM ψ (j + 1) n' • v) + (π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v) := by
    rw [hch, hd, AddChar.map_zero_eq_one, Circle.coe_one, MonoidHom.one_apply, Units.val_one, one_smul,
      map_sub]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩)

end DiscreteGroups.sglob.LConvGenR
end
end

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k) (hξ : ξ (i0 j hj hj1) ≠ 0)
include hξ

theorem coef_eq : (ξ (i0 j hj hj1))⁻¹ * (ξ (i0 j hj hj1) - 1) = 1 - (ξ (i0 j hj hj1))⁻¹ := by
  field_simp

def xA : GL (Fin n) k :=
  ⟨1 + R1 j hj hj1 ξ, 1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ,
    by rw [add_mul, one_mul, mul_sub, mul_one, Matrix.mul_smul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel⟩

theorem topLeft_xA : TopLeft j ((xA j hj hj1 ξ hξ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 + R1 j hj hj1 ξ) i l = _
  rw [Matrix.add_apply, rankOne_top_left_zero j hj hj1 ξ i l h, add_zero]

theorem topLeft_xA_inv : TopLeft j (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i l = _
  rw [Matrix.sub_apply, Matrix.smul_apply, rankOne_top_left_zero j hj hj1 ξ i l h, smul_zero, sub_zero]

theorem rowMul_xA_inv (a : Fin n) (ha : a.val < j) :
    rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a =
      if a = i0 j hj hj1 then 1 else 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i a else 0) =
      (if i = a then ξ a else 0) - (if i = i0 j hj hj1 then vrow j hj hj1 ξ a else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i a else 0) = _
    by_cases hi : i.val < j
    · rw [if_pos hi]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, R1, of_apply, one_apply]
      by_cases hia : i = a <;> by_cases hii : i = i0 j hj hj1
      · subst hia; subst hii; simp; field_simp
      · subst hia; simp [hii]
      · subst hii; simp [hia]; field_simp
      · simp [hia, hii]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact ha)), if_neg (fun e => hi (by rw [e]; exact hi0))]
      ring
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  simp only [vrow, if_pos ha]
  ring

theorem dotj_xA_inv (c : Fin n → k) :
    dotj j (rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) c = c (i0 j hj hj1) := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [dotj, Finset.sum_congr rfl fun a _ => (?_ : _ = if a = i0 j hj hj1 then c a else 0), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]
  by_cases ha : a.val < j
  · rw [if_pos ha, rowMul_xA_inv j hj hj1 ξ hξ a ha]
    split_ifs <;> simp
  · rw [if_neg ha, if_neg (fun e => ha (by rw [e]; exact hi0))]

end RankOne

end DiscreteGroups.sglob.LConvGenM
end
end

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {p : Fin n} (hp : p.val < j) (hne : p ≠ i0 j hj hj1)
include hp

theorem topLeft_single (y : k) (i l : Fin n) (h : j ≤ i.val ∨ j ≤ l.val) :
    Matrix.single p (i0 j hj hj1) y i l = 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  omega

theorem topLeft_elem (y : k) : TopLeft j ((GlobalTheory.RootUp.elem hne y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [GlobalTheory.RootUp.val_elem, Matrix.add_apply, topLeft_single j hj hj1 hp y i l h, add_zero]

theorem topLeft_elem_inv (y : k) :
    TopLeft j (((GlobalTheory.RootUp.elem hne y)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - Matrix.single p (i0 j hj hj1) y) i l = _
  rw [Matrix.sub_apply, topLeft_single j hj hj1 hp y i l h, sub_zero]

theorem rowMul_elem_inv (ξ : Fin n → k) :
    rowMul j ξ (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (i0 j hj hj1) =
      ξ (i0 j hj hj1) + ξ p := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i (i0 j hj hj1) else 0) =
      (if i = i0 j hj hj1 then ξ (i0 j hj hj1) else 0) + (if i = p then ξ p else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - Matrix.single p (i0 j hj hj1) (-1 : k)) i (i0 j hj hj1) else 0) = _
    rw [Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi]
      by_cases h1 : i = i0 j hj hj1
      · subst h1
        have : ¬ (p = i0 j hj hj1) := hne
        simp [this, Ne.symm hne]
      · by_cases h2 : i = p
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact hi0)), if_neg (fun e => hi (by rw [e]; exact hp)),
        add_zero]
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

end DiscreteGroups.sglob.LConvGenM
end
end

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

section Dot

variable {k : Type} [Field k] {n : ℕ}

theorem dotj_add (j : ℕ) (ξ c d : Fin n → k) : dotj j ξ (c + d) = dotj j ξ c + dotj j ξ d := by
  simp only [dotj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_add]

theorem dotj_single (j : ℕ) (ξ : Fin n → k) (a : Fin n) (x : k) :
    dotj j ξ (Pi.single a x) = if a.val < j then ξ a * x else 0 := by
  rw [dotj, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem dotj_update (j : ℕ) (ξ c : Fin n → k) (a : Fin n) (x : k) (hc : c a = 0) :
    dotj j (Function.update ξ a x) c = dotj j ξ c := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = a
  · subst hi; simp [hc]
  · rw [Function.update_of_ne hi]

end Dot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem KUS_empty (j : ℕ) (ξ : Fin n → k) : KUS π ψ j ∅ ξ = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨c, hc, v, rfl⟩
  have : c = 0 := funext fun r => hc r (Finset.notMem_empty r)
  subst this
  have h0 : dotj j ξ (0 : Fin n → k) = 0 := Finset.sum_eq_zero fun i _ => by split_ifs <;> simp
  rw [colU_zero, h0, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

theorem smooth_col (hs : IsSmooth π) (j : ℕ) (hj : j < n) (a : Fin n) (v : V) :
    ∃ s : kˣ, ∀ h ∈ ball s, π (colU j (Pi.single a h)) v = v := by
  by_cases ha : a.val < j
  · have hne : a ≠ (⟨j, hj⟩ : Fin n) := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    have hU : {g : GL (Fin n) k | π g v = v} ∈ nhds (1 : GL (Fin n) k) := (hs v).mem_nhds (by simp)
    have h0 : GlobalTheory.RootUp.elem hne (0 : k) = 1 := Units.ext (by simp [GlobalTheory.RootUp.val_elem])
    have hpre : (GlobalTheory.RootUp.elem hne) ⁻¹' {g : GL (Fin n) k | π g v = v} ∈ nhds (0 : k) :=
      (GlobalTheory.RootUp.continuous_elem hne).continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
    obtain ⟨s, hs'⟩ := exists_cball_subset hpre
    refine ⟨s, fun h hh => ?_⟩
    rw [colU_single_of_lt j hj ha]
    exact hs' hh
  · exact ⟨1, fun h _ => by rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply]⟩

end DiscreteGroups.sglob.LConvGenR
end
end
