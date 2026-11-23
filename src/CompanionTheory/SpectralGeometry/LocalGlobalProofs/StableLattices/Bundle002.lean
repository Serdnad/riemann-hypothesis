module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.Fintype.Card

@[expose] public section

section
end

section
end

section

namespace GlobalTheory.CompanionTheory.CommStep

open Module

theorem commute_of_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (i : Fin (l + 1))
    {y : Module.End ℂ V} (hy : y ∈ Algebra.adjoin ℂ (Set.range a)) : Commute y (a i) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hc j i
  | algebraMap r => exact Algebra.commutes r (a i)
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

theorem adjoin_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) ⊔
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0)) := by
  have hBC : Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ) ≤
      Algebra.adjoin ℂ (Set.range a) :=
    Algebra.adjoin_mono (Set.range_subset_iff.2 fun k => ⟨k.succ, rfl⟩)
  have ha0 : a 0 ∈ Algebra.adjoin ℂ (Set.range a) := Algebra.subset_adjoin ⟨0, rfl⟩
  intro y hy
  rw [Subalgebra.mem_toSubmodule] at hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    induction j using Fin.cases with
    | zero =>
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨1, ?_, ?_⟩)
      · exact (Subalgebra.mem_toSubmodule _).2 (one_mem _)
      · rw [LinearMap.mulRight_apply, one_mul]
    | succ k => exact Submodule.mem_sup_left (Algebra.subset_adjoin ⟨k, rfl⟩)
  | algebraMap r => exact Submodule.mem_sup_left (Subalgebra.algebraMap_mem _ r)
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨p₁, hp₁, z₁, hz₁, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨p₂, hp₂, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨q₁, hq₁, rfl⟩ := Submodule.mem_map.1 hz₁
    obtain ⟨q₂, hq₂, rfl⟩ := Submodule.mem_map.1 hz₂
    rw [Subalgebra.mem_toSubmodule] at hp₁ hp₂ hq₁ hq₂
    rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply]
    have hp₂c : Commute p₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 (hBC hp₂)
    have hq₂c : Commute q₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 hq₂
    have e₁ : q₁ * a 0 * p₂ = q₁ * p₂ * a 0 := by
      rw [mul_assoc, ← hp₂c.eq, ← mul_assoc]
    have e₂ : q₁ * a 0 * (q₂ * a 0) = q₁ * q₂ * a 0 * a 0 := by
      rw [← mul_assoc, mul_assoc q₁, ← hq₂c.eq, ← mul_assoc]
    have key : (p₁ + q₁ * a 0) * (p₂ + q₂ * a 0) =
        p₁ * p₂ + (p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0) * a 0 := by
      rw [add_mul, mul_add, mul_add, e₁, e₂]
      simp only [add_mul, mul_assoc, add_assoc]
    rw [key]
    refine Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).2 (mul_mem hp₁ hp₂))
      (Submodule.mem_map.2 ⟨p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0, ?_, LinearMap.mulRight_apply _ _ _⟩)
    rw [Subalgebra.mem_toSubmodule]
    exact add_mem (add_mem (mul_mem (hBC hp₁) hq₂) (mul_mem hq₁ (hBC hp₂)))
      (mul_mem (mul_mem hq₁ hq₂) ha0)

theorem finrank_map_pow_le {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (k : ℕ) :
    finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
        (LinearMap.mulRight ℂ (a 0 ^ k))) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ (k + 1)))) := by
  have h := Submodule.map_mono (f := LinearMap.mulRight ℂ (a 0 ^ k))
    (GlobalTheory.CompanionTheory.CommStep.adjoin_le_sup a hc)
  have hcomp : (LinearMap.mulRight ℂ (a 0 ^ k)).comp (LinearMap.mulRight ℂ (a 0)) =
      LinearMap.mulRight ℂ (a 0 ^ (k + 1)) :=
    LinearMap.ext fun b => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_succ', mul_assoc]
  rw [Submodule.map_sup, ← Submodule.map_comp, hcomp] at h
  have h1 := Submodule.finrank_mono h
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ))).map
      (LinearMap.mulRight ℂ (a 0 ^ k)))
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
      (LinearMap.mulRight ℂ (a 0 ^ (k + 1))))
  have h3 := Submodule.finrank_map_le (LinearMap.mulRight ℂ (a 0 ^ k))
    (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)))
  rw [Subalgebra.finrank_toSubmodule] at h3
  omega

theorem comm_step : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
    (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) → ∀ x : ℕ,
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      x * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        Module.finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ x))) := by
  intro V _ _ _ l a hc x
  induction x with
  | zero =>
    have hid : LinearMap.mulRight ℂ (a 0 ^ 0) = LinearMap.id :=
      LinearMap.ext fun b => by simp
    rw [hid, Submodule.map_id, Nat.zero_mul, Nat.zero_add, Subalgebra.finrank_toSubmodule]
  | succ x ih =>
    have h := GlobalTheory.CompanionTheory.CommStep.finrank_map_pow_le a hc x
    rw [add_mul, one_mul]
    omega

end GlobalTheory.CompanionTheory.CommStep
end

section

namespace GlobalTheory.CompanionTheory.CommSplit

open Module

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def compr (W W' : Submodule ℂ V) (hc : IsCompl W W') :
    End ℂ V →ₗ[ℂ] End ℂ W where
  toFun b := (W.linearProjOfIsCompl W' hc) ∘ₗ b ∘ₗ W.subtype
  map_add' b c := by ext w; simp
  map_smul' t b := by ext w; simp

lemma compr_of_inv (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) (w : W) : compr W W' hc b w = ⟨b w, hb w w.2⟩ := by
  show W.linearProjOfIsCompl W' hc (b w) = _
  exact Submodule.linearProjOfIsCompl_apply_left hc ⟨b w, hb w w.2⟩

lemma compr_eq_restrict (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) : compr W W' hc b = b.restrict hb := by
  refine LinearMap.ext fun w => ?_
  rw [compr_of_inv W W' hc b hb w]
  rfl

lemma compr_mul (W W' : Submodule ℂ V) (hc : IsCompl W W') (b c : End ℂ V)
    (hcW : ∀ w ∈ W, c w ∈ W) :
    compr W W' hc (b * c) = compr W W' hc b * compr W W' hc c := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, compr_of_inv W W' hc c hcW w]
  rfl

lemma compr_algebraMap (W W' : Submodule ℂ V) (hc : IsCompl W W') (t : ℂ) :
    compr W W' hc (algebraMap ℂ (End ℂ V) t) = algebraMap ℂ (End ℂ W) t := by
  have hb : ∀ w ∈ W, algebraMap ℂ (End ℂ V) t w ∈ W := fun w hw => by
    rw [Module.algebraMap_end_apply]
    exact W.smul_mem t hw
  rw [compr_eq_restrict W W' hc _ hb]
  ext w
  simp [Module.algebraMap_end_apply]

lemma adjoin_compr {l : ℕ} (a : Fin l → End ℂ V) (W W' : Submodule ℂ V) (hc : IsCompl W W')
    (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (b : End ℂ V) (hb : b ∈ Algebra.adjoin ℂ (Set.range a)) :
    (∀ w ∈ W, b w ∈ W) ∧ compr W W' hc b ∈
      Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : End ℂ W)) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨h i, ?_⟩
    rw [compr_eq_restrict W W' hc _ (h i)]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap r =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hw
    · rw [compr_algebraMap]
      exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (hx.1 w hw) (hy.1 w hw)
    · rw [map_add (f := _)]
      exact Subalgebra.add_mem _ hx.2 hy.2
  | mul x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.End.mul_apply]
      exact hx.1 _ (hy.1 w hw)
    · rw [compr_mul W W' hc x y hy.1]
      exact Subalgebra.mul_mem _ hx.2 hy.2

theorem finrank_adjoin_le_add :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
      (a : Fin l → Module.End ℂ V) (W W' : Submodule ℂ V), IsCompl W W' →
      ∀ (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (h' : ∀ i, ∀ w ∈ W', a i w ∈ W'),
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h i) : Module.End ℂ W))) +
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h' i) : Module.End ℂ W'))) := by
  intro V _ _ _ l a W W' hc h h'
  let AW := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : Module.End ℂ W))
  let AW' := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h' i) : Module.End ℂ W'))
  let Φ : Algebra.adjoin ℂ (Set.range a) →ₗ[ℂ] AW × AW' :=
    { toFun := fun b => (⟨compr W W' hc b, (adjoin_compr a W W' hc h b b.2).2⟩,
        ⟨compr W' W hc.symm b, (adjoin_compr a W' W hc.symm h' b b.2).2⟩)
      map_add' := fun b c => by
        ext <;> simp [map_add (f := _)]
      map_smul' := fun t b => by
        ext <;> simp [map_smul] }
  have hinj : Function.Injective Φ := by
    intro b c hbc
    have h1 := congrArg (fun p => (p.1 : Module.End ℂ W)) hbc
    have h2 := congrArg (fun p => (p.2 : Module.End ℂ W')) hbc
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have e1 : (b : Module.End ℂ V) w = (c : Module.End ℂ V) w := by
      have e := LinearMap.congr_fun h1 ⟨w, hw⟩
      rw [compr_of_inv W W' hc _ (adjoin_compr a W W' hc h b b.2).1,
        compr_of_inv W W' hc _ (adjoin_compr a W W' hc h c c.2).1] at e
      exact congrArg Subtype.val e
    have e2 : (b : Module.End ℂ V) w' = (c : Module.End ℂ V) w' := by
      have e := LinearMap.congr_fun h2 ⟨w', hw'⟩
      rw [compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' b b.2).1,
        compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' c c.2).1] at e
      exact congrArg Subtype.val e
    rw [map_add (f := _), map_add (f := _), e1, e2]
  calc Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ (AW × AW') :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℂ AW + Module.finrank ℂ AW' := Module.finrank_prod

end GlobalTheory.CompanionTheory.CommSplit
end

section

namespace GlobalTheory.CompanionTheory.CosetCover

theorem exists_finite_coset_cover :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G),
      IsCompact (K₀ : Set G) → IsOpen (K : Set G) →
        ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  intro G _ _ _ K₀ K hK₀ hK
  classical
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun g : K₀ => (fun x => x * (g : G)⁻¹) ⁻¹' (K : Set G))
    (fun g => hK.preimage (continuous_mul_const _))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : K₀) : G), fun i => (t.equivFin.symm i : K₀).2,
    fun g hg => ?_⟩
  obtain ⟨a, ha, hga⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨t.equivFin ⟨a, ha⟩, g * (a : G)⁻¹, hga, ?_⟩
  simp

end GlobalTheory.CompanionTheory.CosetCover
end

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

def IsUnif (p : Lˣ) : Prop := ‖(p : L)‖ < 1 ∧ ∀ x : L, x ≠ 0 → ∃ a : ℤ, ‖x‖ = ‖(p : L)‖ ^ a

theorem entry_mul {A B : Matrix (Fin n) (Fin n) L} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun l _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha

theorem entry_mul_sub_one {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) (hB : ∀ i j, ‖(B - 1) i j‖ ≤ r) (i j : Fin n) :
    ‖(A * B - 1) i j‖ ≤ r := by
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := entry_mul h0 h0 hA hB i j
  have h2 : r * r ≤ r := by nlinarith
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans h2) (hA i j))


variable (L n) in
def congK (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : Subgroup (GL (Fin n) L) where
  carrier := {k | ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
    ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r}
  mul_mem' := by
    intro a b ha hb i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp [h0]
  inv_mem' := by
    intro a ha i j
    simpa [and_comm] using ha i j

theorem mem_congK {r : ℝ} {h0 : 0 ≤ r} {h1 : r ≤ 1} {k : GL (Fin n) L} :
    k ∈ congK L n r h0 h1 ↔ ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
      ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := Iff.rfl

def dPow (p : Lˣ) (a : Fin n → ℤ) : GL (Fin n) L where
  val := diagonal fun i => ((p ^ a i : Lˣ) : L)
  inv := diagonal fun i => ((p ^ (-a i) : Lˣ) : L)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]

theorem dPow_val (p : Lˣ) (a : Fin n → ℤ) :
    ((dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagonal fun i => ((p ^ a i : Lˣ) : L) := rfl

theorem dPow_add (p : Lˣ) (a b : Fin n → ℤ) : (dPow p (a + b) : GL (Fin n) L) = dPow p a * dPow p b := by
  apply Units.ext
  rw [Units.val_mul, dPow_val, dPow_val, dPow_val, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem dPow_zero (p : Lˣ) : (dPow p (0 : Fin n → ℤ) : GL (Fin n) L) = 1 := by
  apply Units.ext
  simp [dPow_val]

def tExp (n : ℕ) (i : Fin (n + 2)) : Fin n → ℤ :=
  fun j => if (i : ℕ) = n + 1 then -1 else if (j : ℕ) < i then 1 else 0

def tGen (p : Lˣ) (i : Fin (n + 2)) : GL (Fin n) L := dPow p (tExp n i)

end GlobalTheory.CompanionTheory.CartGL
end
end

section

namespace GlobalTheory.CompanionTheory.UGeoGap

theorem exists_gap_of_mem_Icc_top :
    ∀ (n : ℕ) (l : Fin n → ℝ) (L : ℝ), 0 < L → (∀ i, 0 ≤ l i ∧ l i ≤ L) → (∃ i, l i = L) →
      ∃ r : ℕ, r < n ∧ ∀ i, l i < r * (L / (n + 1)) ∨ (r + 1) * (L / (n + 1)) ≤ l i := by
  intro n l L hL _ hex
  obtain ⟨i₀, hi₀⟩ := hex
  by_contra hcon
  push Not at hcon
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hδpos : 0 < L / (n + 1) := div_pos hL hn
  choose f hf using fun r : Fin n => hcon r r.2
  have hinj : Function.Injective f := by
    intro r s hrs
    have h1 := hf r
    have h2 := hf s
    rw [hrs] at h1
    have a1 : ((r : ℕ) : ℝ) < (s : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h1.1 h2.2) hδpos.le
    have a2 : ((s : ℕ) : ℝ) < (r : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h2.1 h1.2) hδpos.le
    have b1 : (r : ℕ) < (s : ℕ) + 1 := by exact_mod_cast a1
    have b2 : (s : ℕ) < (r : ℕ) + 1 := by exact_mod_cast a2
    exact Fin.ext (by omega)
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) i₀
  have h1 := (hf r).2
  rw [hr, hi₀] at h1
  have hr1 : ((r : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast r.2
  have h2 : (((r : ℕ) : ℝ) + 1) * (L / (n + 1)) ≤ n * (L / (n + 1)) :=
    mul_le_mul_of_nonneg_right hr1 hδpos.le
  have h3 : (n : ℝ) * (L / (n + 1)) < (n + 1) * (L / (n + 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hδpos
  have h4 : ((n : ℝ) + 1) * (L / (n + 1)) = L := by
    field_simp
  linarith

end GlobalTheory.CompanionTheory.UGeoGap
end
