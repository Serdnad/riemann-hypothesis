module

import GroundTheory.AutomorphicForms.TensorProductTheorem.GenWindow
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Set

namespace RestrictedTensor

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

def orbitSpan (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (range fun g => ρ g v)
  apply_mem_toSubmodule g x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem mem_orbitSpan_self (ρ : Representation ℂ G V) (v : V) : v ∈ (orbitSpan ρ v).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem orbitSpan_eq_top {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    orbitSpan ρ v = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (orbitSpan ρ v) with h | h
  · exfalso
    apply hv
    have := mem_orbitSpan_self ρ v
    rw [h] at this
    exact this
  · exact h

theorem mem_span_orbit {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (x : V) :
    x ∈ Submodule.span ℂ (range fun g => ρ g v) := by
  exact mem_span_mOrbit hv x

theorem eq_zero_of_forall_apply {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Module.Dual ℂ V} (h : ∀ g, l (ρ g v) = 0) : l = 0 := by
  exact eq_zero_of_forall_apply' hv h

theorem eq_zero_of_forall_apply_act {ρ : Representation ℂ G V} [ρ.IsIrreducible]
    {l : Module.Dual ℂ V} (hl : l ≠ 0) {x : V} (h : ∀ g, l (ρ g x) = 0) : x = 0 := by
  by_contra hx
  exact hl (eq_zero_of_forall_apply (ρ := ρ) hx h)

def orbitMap (ρ : Representation ℂ G V) (v : V) : (G →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun g => ρ g v

theorem orbitMap_apply (ρ : Representation ℂ G V) (v : V) (c : G →₀ ℂ) :
    orbitMap ρ v c = c.sum fun g a => a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_apply]

theorem orbitMap_single (ρ : Representation ℂ G V) (v : V) (g : G) (a : ℂ) :
    orbitMap ρ v (Finsupp.single g a) = a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_single]

theorem orbitMap_mapDomain (ρ : Representation ℂ G V) (v : V) (h : G) (c : G →₀ ℂ) :
    orbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (orbitMap ρ v c) := by
  exact mOrbitMap_mapDomain ρ v h c

theorem range_orbitMap (ρ : Representation ℂ G V) (v : V) :
    LinearMap.range (orbitMap ρ v) = Submodule.span ℂ (range fun g => ρ g v) := by
  rw [orbitMap, Finsupp.range_linearCombination]

theorem linearForm_orbitMap (ρ : Representation ℂ G V) (v : V) (l : Module.Dual ℂ V) (h : G)
    (c : G →₀ ℂ) : l (ρ h (orbitMap ρ v c)) = c.sum fun g a => a * l (ρ (h * g) v) := by
  exact linearForm_mOrbitMap ρ v l h c

theorem nonempty_equiv_of_matrixCoeff_eq {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Module.Dual ℂ V} {w : W}
    {m : Module.Dual ℂ W} (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  exact nonempty_equiv_of_matrixCoeff_eq' h hne

end RestrictedTensor

end GroundTheory.Automorphic
