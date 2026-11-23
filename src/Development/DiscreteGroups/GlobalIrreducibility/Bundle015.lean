module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle005
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle009
import Development.DiscreteGroups.GlobalIrreducibility.LConvGlue
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle014
import Development.DiscreteGroups.GlobalIrreducibility.Bundle013
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepM
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem small_fix (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) (v₁ : V₁) (v₂ : V₂) (i j : Fin (m + 1)) (h : i ≠ j) :
    {t : k | π₁ (tv i j h (-t)) v₁ = v₁ ∧ π₂ (tv i j h (-t)) v₂ = v₂} ∈ 𝓝 (0 : k) := by
  have hc : Continuous fun t : k => tv i j h (-t) := (continuous_tv i j h).comp continuous_neg
  refine IsOpen.mem_nhds (((hs₁ v₁).preimage hc).inter ((hs₂ v₂).preimage hc)) ?_
  simp [tv_zero]

theorem last_ne_zero (hm : 0 < m) : Fin.last m ≠ (0 : Fin (m + 1)) := fun e => by
  have := congrArg Fin.val e
  simp at this
  omega

theorem transvection_apply_same (i j : Fin (m + 1)) (h : i ≠ j) (t : k) : Matrix.transvection i j t i j = t := by
  simp [Matrix.transvection, Matrix.one_apply_ne h]

theorem centralChar_eq (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω₁ ω₂ : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (h0 : l₁ v₁ ≠ 0) : ω₁ = ω₂ := by
  have hc : l₁ v₁ = l₂ v₂ := by
    have := hX 1
    rwa [corner_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
  have hL := last_ne_zero hm
  have hO := small_fix hs₁ hs₂ v₁ v₂ _ _ hL
  have key : ∀ t : k, ∀ ht : t ≠ 0, t ∈ {t : k | π₁ (tv _ _ hL (-t)) v₁ = v₁ ∧ π₂ (tv _ _ hL (-t)) v₂ = v₂} →
      ω₁ (Units.mk0 t ht) = ω₂ (Units.mk0 t ht) := by
    intro t ht hmem
    have hent : (((tv _ _ hL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 =
        (Units.mk0 t ht : k) := by
      rw [val_tv_inv, neg_neg, transvection_apply_same _ _ hL, Units.val_mk0]
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX _ _ hent
    rw [hmem.1, hmem.2, ← hc] at this
    exact Units.ext (mul_right_cancel₀ h0 this)
  refine MonoidHom.ext fun a => ?_
  obtain ⟨t, ht, htO, hatO⟩ := exists_small hO (a : k)
  have hat : (a : k) * t ≠ 0 := mul_ne_zero a.ne_zero ht
  have e : Units.mk0 ((a : k) * t) hat = a * Units.mk0 t ht := Units.ext (by simp)
  have h1 := key _ hat hatO
  rw [e, map_mul, map_mul, key _ ht htO] at h1
  exact mul_right_cancel h1

theorem agree_all (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω) (h₂ : HasCentralChar π₂ ω) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  have step : ∀ g : GL (Fin (m + 1)) k,
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 ≠ 0 →
      l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
    intro g hg
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX g (Units.mk0 _ hg) rfl
    exact mul_left_cancel₀ (ω (Units.mk0 _ hg)).ne_zero this
  by_cases hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 0
  swap
  · exact step g hg
  obtain ⟨j, hj⟩ : ∃ j, ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) j 0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h1 := congrFun (congrFun g.mul_inv 0) 0
    rw [Matrix.mul_apply] at h1
    simp [hall] at h1
  have hjL : Fin.last m ≠ j := fun e => hj (e ▸ hg)
  obtain ⟨t, ht, htO, -⟩ := exists_small (small_fix hs₁ hs₂ v₁ v₂ _ _ hjL) 1
  have hent : (((g * tv _ _ hjL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      (Fin.last m) 0 ≠ 0 := by
    rw [mul_inv_rev, Units.val_mul, val_tv_inv, neg_neg, Matrix.transvection_mul_apply_same, hg, zero_add]
    exact mul_ne_zero ht hj
  have := step _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, htO.1, htO.2] at this

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

def chM (m : ℕ) (g : GL (Fin n) k) : ℂ := ((ψ (sdS m (g : Matrix (Fin n) (Fin n) k)) : Circle) : ℂ)

def KN (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ g ∈ Nset m, ∃ v : V, w = π g v - chM ψ m g • v}

def KUS (j : ℕ) (S : Finset (Fin n)) (ξ : Fin n → k) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ c : Fin n → k, (∀ r ∉ S, c r = 0) ∧ ∃ v : V,
    w = π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v}

theorem conj_apply (x g : GL (Fin n) k) (v : V) : π x (π g v) = π (x * g * x⁻¹) (π x v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem KN_stable (j : ℕ) (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {w : V} (hw : w ∈ KN π ψ (j + 1)) :
    π x w ∈ KN π ψ (j + 1) := by
  refine (Submodule.span_le.2 ?_ : KN π ψ (j + 1) ≤ (KN π ψ (j + 1)).comap (π x)) hw
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := good_conj x hx hy hg
  refine Submodule.subset_span ⟨x * g * x⁻¹, h1, π x v, ?_⟩
  rw [map_sub, map_smul, conj_apply, chM, chM, h2]

theorem colU_comm (j : ℕ) (c d : Fin n → k) : colU j c * colU j d = colU j d * colU j c := by
  rw [← colU_add, ← colU_add, add_comm]

theorem KUS_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V} (hw : w ∈ KUS π ψ j S ξ) :
    π (colU j d) w ∈ KUS π ψ j S ξ := by
  refine (Submodule.span_le.2 ?_ : KUS π ψ j S ξ ≤ (KUS π ψ j S ξ).comap (π (colU j d))) hw
  rintro _ ⟨c, hc, v, rfl⟩
  refine Submodule.subset_span ⟨c, hc, π (colU j d) v, ?_⟩
  rw [map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, colU_comm, map_mul, Module.End.mul_apply]

theorem W_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ) : π (colU j d) w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j d) (good_colU_inv j d) ha)
    (KUS_stable π ψ j S ξ d hb)

theorem KN_top (m : ℕ) (hm : n ≤ m) : KN π ψ m = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  have hg1 : g = 1 := by
    ext i l
    rw [hg i l (Or.inr (by omega)), Units.val_one]
  have hs : sdS m ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg (by omega)]
  rw [hg1, chM, hs, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

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

theorem conj_colU (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (c : Fin n → k) :
    x⁻¹ * colU j c * x = colU j (colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hYX : Y * X = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYC : Y * colM j c = colM j (colMul j Y c) := by
    ext i b
    rw [Matrix.mul_apply, colM_apply]
    by_cases hb : b.val = j
    · simp only [colM_apply, hb, and_true]
      by_cases hi : i.val < j
      · rw [if_pos hi, colMul]
        exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun a _ => ?_
        split_ifs with ha
        · rw [hy i a (Or.inl (by omega)), one_apply_ne (by intro e; rw [e] at hi; omega), zero_mul]
        · rw [mul_zero]
    · simp [colM_apply, hb]
  have hCX : ∀ d : Fin n → k, colM j d * X = colM j d := by
    intro d
    ext i l
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [hx _ l (Or.inl le_rfl)]
      by_cases hl : (⟨j, hj⟩ : Fin n) = l
      · rw [← hl, one_apply_eq, mul_one]
      · rw [one_apply_ne hl, mul_zero, colM_apply, if_neg (fun h => hl (Fin.ext h.2.symm))]
    · intro b _ hb
      rw [colM_apply, if_neg (fun h => hb (Fin.ext h.2)), zero_mul]
    · simp
  ext : 1
  rw [Units.val_mul, Units.val_mul, val_colU, val_colU, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hYX, hYC, hCX]

def i0 (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) : Fin n := ⟨j - 1, by omega⟩

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k)

def vrow : Fin n → k := fun l => if l.val < j then ξ l - (if l = i0 j hj hj1 then 1 else 0) else 0

def R1 : Matrix (Fin n) (Fin n) k := Matrix.of fun i l => if i = i0 j hj hj1 then vrow j hj hj1 ξ l else 0

theorem rankOne_mul_self : R1 j hj hj1 ξ * R1 j hj hj1 ξ = (vrow j hj hj1 ξ (i0 j hj hj1)) • R1 j hj hj1 ξ := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (i0 j hj hj1)]
  · simp only [R1, of_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    split_ifs <;> ring
  · intro b _ hb; simp [R1, hb]
  · simp

theorem rowVector_at_index : vrow j hj hj1 ξ (i0 j hj hj1) = ξ (i0 j hj hj1) - 1 := by
  simp [vrow, i0, show j - 1 < j by omega]

theorem rankOne_top_left_zero : ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → R1 j hj hj1 ξ i l = 0 := by
  intro i l h
  simp only [R1, of_apply]
  split_ifs with hi
  · have : ¬ l.val < j := by rw [hi] at h; simp [i0] at h; omega
    simp [vrow, this]
  · rfl

end RankOne

end DiscreteGroups.sglob.LConvGenM
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem form_eq_zero_of_self {M : Type} [AddCommGroup M] [Module ℂ M] {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hh : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (hp : ∀ x, 0 ≤ (B x x).re) {z : M} (hz : B z z = 0)
    (x : M) : B z x = 0 := by
  by_contra ha
  have hn : 0 < Complex.normSq (B z x) := Complex.normSq_pos.2 ha
  have hxz : B x z = (starRingEnd ℂ) (B z x) := (hh z x).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B z x) = (B x x).re + 1 :=
    ⟨((B x x).re + 1) / (2 * Complex.normSq (B z x)), by field_simp⟩
  have key := hp (x + ((-(t : ℂ)) * B z x) • z)
  have e1 : B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z) =
      B x x + (-(t : ℂ)) * B z x * (starRingEnd ℂ) (B z x) +
        (starRingEnd ℂ) (-(t : ℂ) * B z x) * B z x := by
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, hz, hxz]
    ring
  have e2 : (B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z)).re =
      (B x x).re - 2 * t * Complex.normSq (B z x) := by
    rw [e1]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg,
      Complex.conj_ofReal, Complex.normSq_apply]
    ring
  linarith

theorem circle_conj_mul (z : Circle) : (starRingEnd ℂ) (z : ℂ) * z = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

theorem conj_mul_self_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem conj_psi (c : k) : (starRingEnd ℂ) ((ψ c : Circle) : ℂ) = ((ψ⁻¹ c : Circle) : ℂ) := by
  rw [AddChar.inv_apply', Circle.coe_inv_eq_conj]

theorem superDiag_inv {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : superDiag u⁻¹ = -superDiag u := by
  have h := superDiag_mul ((unipB k (Fin m)).inv_mem hu) hu
  rw [inv_mul_cancel, superDiag_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem superDiag_conj {u n : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (hn : n ∈ unipB k (Fin m)) :
    superDiag (u⁻¹ * n * u) = superDiag n := by
  have hu' := (unipB k (Fin m)).inv_mem hu
  rw [superDiag_mul ((unipB k (Fin m)).mul_mem hu' hn) hu, superDiag_mul hu' hn, superDiag_inv hu]
  ring

theorem delta_one {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : (delta ψ K : GL (Fin m) k → ℂ) 1 = 1 := by
  have := delta_mul hK (unipB k (Fin m)).one_mem K.one_mem
  rw [mul_one, superDiag_one, AddChar.map_zero_eq_one, Circle.coe_one] at this
  exact this

theorem delta_ne_zero {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : delta ψ K ≠ 0 := fun h => by
  have := delta_one hK
  rw [h] at this
  exact zero_ne_one this

theorem delta_eq_of_le {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (g : GL (Fin m) k) (hg : (delta ψ K' : GL (Fin m) k → ℂ) g ≠ 0) :
    (delta ψ K : GL (Fin m) k → ℂ) g = (delta ψ K' : GL (Fin m) k → ℂ) g := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K', g = u * κ := by
    by_contra h
    exact hg (delta_eq_zero h)
  rw [delta_mul hK hu (hle hκ), delta_mul hK' hu hκ]

theorem good_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) : Good ψ (K.map (MulAut.conj u).toMonoidHom) := by
  have e : ((K.map (MulAut.conj u).toMonoidHom : Subgroup (GL (Fin m) k)) : Set (GL (Fin m) k)) =
      (fun y => u⁻¹ * y * u) ⁻¹' K := Set.ext fun _ => mem_conj
  have hc : Continuous fun κ : GL (Fin m) k => u * κ * u⁻¹ := by fun_prop
  refine ⟨?_, ?_, fun n hn hnK => ?_⟩
  · rw [e]
    exact hK.1.preimage (by fun_prop)
  · rw [Subgroup.coe_map]
    exact hK.2.1.image hc
  · rw [← superDiag_conj hu hn]
    exact hK.2.2 _ ((unipB k (Fin m)).mul_mem ((unipB k (Fin m)).mul_mem
      ((unipB k (Fin m)).inv_mem hu) hn) hu) (mem_conj.1 hnK)

end DiscreteGroups.sglob.LConv

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem delta_avg {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (L₁ L₂ : WT (m := m) ψ →ₗ[ℂ] ℂ) (h₁ : ∀ κ ∈ K, ∀ x, L₁ (rhoW ψ κ x) = L₁ x)
    (h₂ : ∀ κ ∈ K, ∀ x, L₂ (rhoW ψ κ x) = L₂ x) :
    L₁ (delta ψ K') * L₂ (delta ψ K) = L₁ (delta ψ K) * L₂ (delta ψ K') := by
  have hKc : CompactSpace K := isCompact_iff_compactSpace.1 hK.2.1
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.1.preimage continuous_subtype_val
  have : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (K ⧸ K'.subgroupOf K) := Fintype.ofFinite _
  set P : WT (m := m) ψ := ∑ q : K ⧸ K'.subgroupOf K,
    rhoW ψ ((Quotient.out q : K) : GL (Fin m) k) (delta ψ K') with hP
  have hrep : ∀ a b : K, b⁻¹ * a ∈ K'.subgroupOf K →
      rhoW ψ (a : GL (Fin m) k) (delta ψ K') = rhoW ψ (b : GL (Fin m) k) (delta ψ K') := by
    intro a b hab
    have e : (a : GL (Fin m) k) = b * ((b⁻¹ * a : K) : GL (Fin m) k) := by simp
    rw [e, map_mul, Module.End.mul_apply, rhoW_delta (Subgroup.mem_subgroupOf.1 hab)]
  have hfix : ∀ κ ∈ K, rhoW ψ κ P = P := by
    intro κ hκ

    rw [hP, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨κ, hκ⟩ : K)) _ _ fun q => ?_
    rw [MulAction.toPerm_apply, ← Module.End.mul_apply, ← map_mul]
    have e : (QuotientGroup.mk (Quotient.out ((⟨κ, hκ⟩ : K) • q)) : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk ((⟨κ, hκ⟩ : K) * Quotient.out q) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    have := hrep ((⟨κ, hκ⟩ : K) * Quotient.out q) (Quotient.out ((⟨κ, hκ⟩ : K) • q)) (QuotientGroup.eq.1 e)
    simpa using this
  have hL : ∀ L : WT (m := m) ψ →ₗ[ℂ] ℂ, (∀ κ ∈ K, ∀ x, L (rhoW ψ κ x) = L x) →
      L P = (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) * L (delta ψ K') := by
    intro L hL

    rw [hP, map_sum, Finset.sum_congr rfl fun q _ => hL _ (Quotient.out q).2 _, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hs : ∀ g, (P : GL (Fin m) k → ℂ) g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ := by
    intro g hg
    rw [hP, Submodule.coe_sum, Finset.sum_apply] at hg
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    rw [rhoW_apply] at hq
    by_contra hno
    refine hq (delta_eq_zero ?_)
    rintro ⟨u, hu, κ', hκ', he⟩
    exact hno ⟨u, hu, κ' * ((Quotient.out q : K) : GL (Fin m) k)⁻¹,
      K.mul_mem (hle hκ') (K.inv_mem (Quotient.out q).2), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩
  obtain ⟨s, hPs⟩ : ∃ s : ℂ, P = s • delta ψ K := ⟨_, eq_smul_delta hK P hfix hs⟩
  have a1 := hL L₁ h₁
  have a2 := hL L₂ h₂
  rw [hPs, map_smul, smul_eq_mul] at a1 a2
  have c0 : (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ c0
  linear_combination (-L₂ (delta ψ K)) * a1 + L₁ (delta ψ K) * a2

def pairI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) : ℂ :=
  I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g


variable (ψ) in
def formI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (pairI I)
    (fun x x' y => by
      simp only [pairI]
      rw [← map_add (f := _)]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]; ring)
    (fun x y y' => by
      simp only [pairI]
      rw [← map_add (f := _)]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem formI_apply (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) :
    formI ψ I x y = I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g := rfl

end DiscreteGroups.sglob.LConv

end
end
