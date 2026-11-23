module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
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

@[expose] public section

section

namespace GlobalTheory.InertiaRootOfUnity

theorem eq_one_of_val_sub_lt {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (N : ℕ) (hN : ¬ w (N : K) < 1) (u : K) (hu : u ^ N = 1) (h : w (u - 1) < 1) : u = 1 := by
  by_contra hne
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hw1 : w u = 1 := by
    have h' := Valuation.map_add_eq_of_lt_right w (x := u - 1) (y := 1) (by rw [map_one]; exact h)
    rwa [sub_add_cancel, map_one] at h'
  have hpow : ∀ i : ℕ, w (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hr : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
      rw [hr]
      refine Valuation.map_add_lt w ?_ h
      rw [map_mul, hw1, one_mul]
      exact ih
  have hsum : ∑ i ∈ Finset.range N, u ^ i = 0 := by
    have hg := geom_sum_mul u N
    rw [hu, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hx
  have hNeq : (N : K) = -∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  apply hN
  rw [hNeq, Valuation.map_neg]
  exact w.map_sum_lt one_ne_zero fun i _ => hpow i

theorem inertia_fixes_root_of_unity {Ω : Type} [Field Ω] [Algebra ℚ Ω] (N : ℕ) (v : GlobalTheory.Ord2.Pl)
    (B : ValuationSubring Ω) (hB : Formalism.ConjugateSelfDual.IsPlaceOver B v)
    (hN : ¬ ((N : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal))
    (s : Formalism.ConjugateSelfDual.G ℚ Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine B) (ζ : Ω) (hζ : ζ ^ N = 1) : s ζ = ζ := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simpa using v.asIdeal.zero_mem)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow hN0] at hζ
  have hwζ : B.valuation ζ = 1 := by
    have hp : B.valuation ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (B.valuation ζ) 1 with hlt | heq | hgt
    · exact absurd hp (pow_lt_one₀ zero_le' hlt hN0).ne
    · exact heq
    · exact absurd hp (one_lt_pow₀ hgt hN0).ne'
  have hI := (ReciprocityTheory.Gal.mem_Ine.mp hs).2 ζ hwζ.le
  have hsζ : s ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
  have hone := eq_one_of_val_sub_lt B.valuation N ?_ (s ζ * ζ⁻¹) ?_ ?_
  · exact (mul_inv_eq_one₀ hζ0).mp hone
  · intro hlt
    exact hN ((hB N).mp (by simpa using hlt))
  · rw [mul_pow, hsζ, inv_pow, hζ, inv_one, mul_one]
  · have hr : s ζ * ζ⁻¹ - 1 = (s ζ - ζ) * ζ⁻¹ := by field_simp
    rw [hr, map_mul, map_inv₀, hwζ, inv_one, mul_one]
    exact hI

end GlobalTheory.InertiaRootOfUnity
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ZeroSubmodule

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact (Nat.Prime l)]

theorem colRep_apply_of_one (V : GlobalTheory.Ord2.R2 Ω l) (s : G ℚ Ω)
    (hs : (V : G ℚ Ω → GL (Fin 2) (Qbar l)) s = 1) (v : Fin 2 → Qbar l) :
    UpperTheory.V.Loc.colRep V s v = v := by
  show Matrix.toLin' ((V s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) v = v
  rw [hs]
  simp

def zeroSub (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : Subgroup (G ℚ Ω) where
  carrier := {s | s ∈ H ∧ x s = 0}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
    rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
    simpa using h
  mul_mem' := by
    rintro s t ⟨hs, hs0⟩ ⟨ht, ht0⟩
    refine ⟨H.mul_mem hs ht, ?_⟩
    rw [((mem_Z1_iff_cocycle _ x).1 hx).2 s t, colRep_apply_of_one V s (hV s hs), hs0, ht0, add_zero]
  inv_mem' := by
    rintro s ⟨hs, hs0⟩
    refine ⟨H.inv_mem hs, ?_⟩
    have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 s s⁻¹
    rw [mul_inv_cancel, colRep_apply_of_one V s (hV s hs), hs0, zero_add] at h
    have h1 : x 1 = 0 := by
      have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
      rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
      simpa using h
    rw [← h, h1]

theorem cocycle_one (V : GlobalTheory.Ord2.R2 Ω l) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : x 1 = 0 := by
  have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
  rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
  simpa using h

theorem zeroSub_normal (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hH : H.Normal) (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : (zeroSub V H x hV hx).Normal := by
  constructor
  rintro s ⟨hs, hs0⟩ g
  refine ⟨hH.conj_mem s hs g, ?_⟩
  have hc := ((mem_Z1_iff_cocycle _ x).1 hx).2
  rw [hc (g * s) g⁻¹, hc g s, hs0, map_zero, add_zero, map_mul, Module.End.mul_apply,
    colRep_apply_of_one V s (hV s hs), ← hc g g⁻¹, mul_inv_cancel, cocycle_one V x hx]

theorem zeroSub_isClosed (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hHc : IsClosed (H : Set (G ℚ Ω))) (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : IsClosed (zeroSub V H x hV hx : Set (G ℚ Ω)) := by
  have : (zeroSub V H x hV hx : Set (G ℚ Ω)) = (H : Set (G ℚ Ω)) ∩ x ⁻¹' {0} := rfl
  rw [this]
  exact hHc.inter (isClosed_singleton.preimage ((mem_Z1_iff_cocycle _ x).1 hx).1)

theorem main : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : Algebra ℚ Ω] {l : ℕ} [inst_2 : Fact (Nat.Prime l)] (S : Set GlobalTheory.Ord2.Pl) (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (Formalism.ConjugateSelfDual.G ℚ Ω)) (x : Formalism.ConjugateSelfDual.G ℚ Ω → Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l), Subgroup.Normal H → IsClosed (↑H : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) → (∀ a ∈ H, (V : Formalism.ConjugateSelfDual.G ℚ Ω → GL (Fin (2 : ℕ)) (Formalism.ConjugateSelfDual.Qbar l)) a = (1 : GL (Fin (2 : ℕ)) (Formalism.ConjugateSelfDual.Qbar l))) → x ∈ ReciprocityTheory.Gal.Z1 (UpperTheory.V.Loc.colRep V) → (∀ v ∉ S, ∀ (B : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver B v → ∀ s ∈ ReciprocityTheory.Gal.Ine B, s ∈ H ∧ x s = (0 : Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l)) → ∀ a ∈ ReciprocityTheory.Gal.NS Ω S, x a = (0 : Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l) := by
  intro Ω _ _ l _ S V H x hH hHc hV hx hI a ha
  haveI := zeroSub_normal V H x hH hV hx
  have hle : NS Ω S ≤ zeroSub V H x hV hx := by
    apply Subgroup.topologicalClosure_minimal _ _ (zeroSub_isClosed V H x hHc hV hx)
    apply Subgroup.normalClosure_le_normal
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs
    obtain ⟨v, hv, B, hB, hsB⟩ := hs
    exact hI v hv B hB s hsB
  exact (hle ha).2

end GlobalTheory.ZeroSubmodule
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.LocChar.unit_of_integral :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  intro l _ Ω _ _ c A k k' hcont hint hmul

  have heps : ∀ s : G ℚ Ω, eps l s * algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    intro s
    have h1 : algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (((cycBar ℚ Ω l s)⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← map_inv]
      simp [cycBar, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
    rw [h1, eps]
    exact Units.mul_inv _
  have hmem : ∀ s : G ℚ Ω, algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O :=
    fun s => c.O.algebraMap_mem _
  let f : ↥(Dec (F := ℚ) A) → c.Oˣ := fun g =>
    Units.mkOfMulEqOne ⟨k g, (hint g g.2).1⟩
      (⟨k' g, (hint g g.2).2.1⟩ * ⟨_, hmem g⟩) (by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← mul_assoc, (hint g g.2).2.2]
        exact heps g)
  have hf : ∀ g, (((f g : c.Oˣ) : c.O) : Qbar l) = k g := fun g => rfl
  have hone : k 1 = 1 := by
    have h11 := hmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [one_mul] at h11
    have hu : IsUnit (((f 1 : c.Oˣ) : c.O) : Qbar l) := by
      have : IsUnit ((f 1 : c.Oˣ) : c.O) := Units.isUnit _
      exact this.map c.O.val
    rw [hf, OneMemClass.coe_one] at hu
    exact hu.mul_left_cancel (by rw [mul_one]; exact h11.symm)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, hf⟩
  · ext
    change k _ = 1
    rw [OneMemClass.coe_one, hone]
  · intro g h
    ext
    change k _ = k _ * k _
    rw [Subgroup.coe_mul]
    exact hmul g g.2 h h.2
  · have hc : Continuous ((Dec (F := ℚ) A : Set (G ℚ Ω)).restrict k) :=
      continuousOn_iff_continuous_restrict.mp hcont
    exact hc.subtype_mk (fun g => (hint g g.2).1)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.IntNorm

theorem norm_intCast_qbar (l : ℕ) [Fact l.Prime] (d : ℤ) :
    ‖(d : Qbar l)‖ = ‖(d : ℚ_[l])‖ := by
  have h : (d : Qbar l) = ((d : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends]

theorem norm_l_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem not_cg_int_mul_pow (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hlt : |d| < (l : ℤ) ^ t) : ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  intro h
  unfold Cg at h
  rw [sub_zero, norm_mul, norm_pow, norm_pow, pow_add] at h
  have hlpos : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ := by
    rw [norm_l_qbar]; have := (Fact.out : l.Prime).pos; positivity
  have hk : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ ^ k := pow_pos hlpos k
  have h1 : ‖(d : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ t := le_of_mul_le_mul_right h hk
  rw [norm_intCast_qbar, norm_l_qbar] at h1
  have h2 : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(t : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact h1
  have h3 : ((l : ℤ) ^ t) ∣ d := (Padic.norm_int_le_pow_iff_dvd d t).mp h2
  have h4 : ((l : ℤ) ^ t) ≤ |d| := by
    have := Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr h3)
    exact this
  omega

end GlobalTheory.Ord2.IntNorm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCount

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def SelN (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (V : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  Coc1 c n V ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧
      Cob1 c n V (Ine (F := ℚ) B) z) ∧
    (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat V s 1 1 * x - x))

end GlobalTheory.Ord2.GwCount
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.VanishNarrow

open Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]


omit [Fact l.Prime] in
theorem valuation_lt_one {A : ValuationSubring Ω} (h : OverL l A) : A.valuation (l : Ω) < 1 := by
  obtain ⟨v, hv, hl⟩ := h
  have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
  simpa using h1

end GlobalTheory.Ord2.VanishNarrow

namespace GlobalTheory.Ord2

end GlobalTheory.Ord2

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def MemE (c : Coef l) (x : Qbar l) : Prop := ∃ k : ℕ, (l : Qbar l) ^ k * x ∈ c.O

def VecE (c : Coef l) (y : Fin 2 → Qbar l) : Prop := ∃ k : ℕ, ∀ i, (l : Qbar l) ^ k * y i ∈ c.O

theorem natPow_mem (c : Coef l) (k : ℕ) : (l : Qbar l) ^ k ∈ c.O :=
  c.O.pow_mem (c.O.natCast_mem l) k

theorem pow_mul_mem_add (c : Coef l) {x : Qbar l} {k : ℕ} (h : (l : Qbar l) ^ k * x ∈ c.O) (j : ℕ) :
    (l : Qbar l) ^ (k + j) * x ∈ c.O := by
  rw [pow_add, mul_comm ((l : Qbar l) ^ k), mul_assoc]
  exact c.O.mul_mem (natPow_mem c j) h

theorem memE_add {c : Coef l} {x y : Qbar l} (hx : MemE c x) (hy : MemE c y) : MemE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, ?_⟩
  have h2 := pow_mul_mem_add c hj k
  rw [add_comm j k] at h2
  rw [mul_add]
  exact c.O.add_mem (pow_mul_mem_add c hk j) h2

theorem memE_neg {c : Coef l} {x : Qbar l} (hx : MemE c x) : MemE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [mul_neg]; exact c.O.neg_mem hk⟩

theorem vecE_add {c : Coef l} {x y : Fin 2 → Qbar l} (hx : VecE c x) (hy : VecE c y) : VecE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, fun i => ?_⟩
  have h2 := pow_mul_mem_add c (hj i) k
  rw [add_comm j k] at h2
  rw [Pi.add_apply, mul_add]
  exact c.O.add_mem (pow_mul_mem_add c (hk i) j) h2

theorem vecE_neg {c : Coef l} {x : Fin 2 → Qbar l} (hx : VecE c x) : VecE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, fun i => by rw [Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk i)⟩

def divSelCoc (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∃ k : ℕ, ∀ s i, (l : Qbar l) ^ k * z s i ∈ c.O) ∧
    (∀ s t i, z (s * t) i - z s i - (mat W s *ᵥ z t) i ∈ c.O) ∧
    (∀ s, ∀ᶠ t in nhds s, ∀ i, z t i - z s i ∈ c.O) ∧
    (∀ a ∈ (toGS Ω (S : Set Pl)).ker, ∀ i, z a i ∈ c.O) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ i, z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
    (∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, z s 1 - (mat W s 1 1 * y - y) ∈ c.O)}
  add_mem' := by
    rintro z w ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩ ⟨⟨k', hk'⟩, h2', h3', h4', h5', ⟨y', hy', h6'⟩⟩
    refine ⟨⟨k + k', fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨y + y', memE_add hy hy', fun s hs => ?_⟩⟩
    · have h := pow_mul_mem_add c (hk' s i) k
      rw [add_comm k' k] at h
      rw [Pi.add_apply, Pi.add_apply, mul_add]
      exact c.O.add_mem (pow_mul_mem_add c (hk s i) k') h
    · have e : (z + w) (s * t) i - (z + w) s i - (mat W s *ᵥ (z + w) t) i =
          (z (s * t) i - z s i - (mat W s *ᵥ z t) i) + (w (s * t) i - w s i - (mat W s *ᵥ w t) i) := by
        simp only [Pi.add_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (h2 s t i) (h2' s t i)
    · filter_upwards [h3 s, h3' s] with t ht ht' i
      have e : (z + w) t i - (z + w) s i = (z t i - z s i) + (w t i - w s i) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (ht i) (ht' i)
    · rw [Pi.add_apply, Pi.add_apply]; exact c.O.add_mem (h4 a ha i) (h4' a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      obtain ⟨u', hv, hv'⟩ := h5' q hq hl B hB
      refine ⟨u + u', vecE_add hu hv, fun s hs i => ?_⟩
      have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
          (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
        simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (hu' s hs i) (hv' s hs i)
    · have e : (z + w) s 1 - (mat W s 1 1 * (y + y') - (y + y')) =
          (z s 1 - (mat W s 1 1 * y - y)) + (w s 1 - (mat W s 1 1 * y' - y')) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (h6 s hs) (h6' s hs)
  zero_mem' := by
    refine ⟨⟨0, fun s i => by simp⟩, fun s t i => by simp, fun s => Filter.Eventually.of_forall fun t i => by simp,
      fun a _ i => by simp, fun q _ _ B _ => ⟨0, ⟨0, fun i => by simp⟩, fun s _ i => by simp⟩, ⟨0, ⟨0, by simp⟩, fun s _ => by simp⟩⟩
  neg_mem' := by
    rintro z ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩
    refine ⟨⟨k, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨-y, memE_neg hy, fun s hs => ?_⟩⟩
    · rw [Pi.neg_apply, Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk s i)
    · have e : (-z) (s * t) i - (-z) s i - (mat W s *ᵥ (-z) t) i = -(z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
        simp only [Pi.neg_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (h2 s t i)
    · filter_upwards [h3 s] with t ht i
      have e : (-z) t i - (-z) s i = -(z t i - z s i) := by simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (ht i)
    · rw [Pi.neg_apply, Pi.neg_apply]; exact c.O.neg_mem (h4 a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      refine ⟨-u, vecE_neg hu, fun s hs i => ?_⟩
      have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
        simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (hu' s hs i)
    · have e : (-z) s 1 - (mat W s 1 1 * (-y) - (-y)) = -(z s 1 - (mat W s 1 1 * y - y)) := by
        simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (h6 s hs)

def divCob (c : Coef l) (W : R2 Ω l) : AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s i, z s i - (mat W s *ᵥ y - y) i ∈ c.O}
  add_mem' := by
    rintro z w ⟨u, hu, hu'⟩ ⟨u', hv, hv'⟩
    refine ⟨u + u', vecE_add hu hv, fun s i => ?_⟩
    have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
        (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
      simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
    rw [e]; exact c.O.add_mem (hu' s i) (hv' s i)
  zero_mem' := ⟨0, ⟨0, fun i => by simp⟩, fun s i => by simp⟩
  neg_mem' := by
    rintro z ⟨u, hu, hu'⟩
    refine ⟨-u, vecE_neg hu, fun s i => ?_⟩
    have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
      simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
    rw [e]; exact c.O.neg_mem (hu' s i)

abbrev DivSel (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) : Type :=
  ↥(divSelCoc c W S A) ⧸ (divCob c W).addSubgroupOf (divSelCoc c W S A)

theorem divSel_torsion (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    ∀ x : DivSel c W S A, ∃ n : ℕ, l ^ n • x = 0 := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    obtain ⟨k, hk⟩ := z.2.1
    refine ⟨k, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨0, ⟨0, fun i => by simp⟩, fun s i => ?_⟩
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul, Matrix.mulVec_zero, sub_zero, Pi.zero_apply]
    push_cast
    exact hk s i

end GlobalTheory.Ord2

end
end
