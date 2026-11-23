module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle126
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle228
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle222
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SupModel

variable {k G : Type} [Field k] [Group G]

theorem isHom_comp {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) :=
  fun s x => by simp only [LinearMap.comp_apply]; rw [hf, hg]

theorem isHom_add {A B : Ob k G} {f g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    (hf : IsHom A B f) (hg : IsHom A B g) : IsHom A B (f + g) :=
  fun s x => by simp only [LinearMap.add_apply, map_add (f := _)]; rw [hf, hg]

theorem exists_sum (A B : Ob k G) : ∃ (C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), IsHom A C i ∧ IsHom B C j ∧ Function.Bijective (i.coprod j) := by
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.prod B.ρ)
  refine ⟨C, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e.toLinearMap ∘ₗ LinearMap.inr k _ _, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · have : (e.toLinearMap ∘ₗ LinearMap.inl k _ _).coprod (e.toLinearMap ∘ₗ LinearMap.inr k _ _)
        = e.toLinearMap := by
      rw [← LinearMap.comp_coprod, LinearMap.coprod_inl_inr, LinearMap.comp_id]
    rw [this]; exact e.bijective

theorem exists_proj {A B C : Ob k G} {i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    {j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hi : IsHom A C i) (hj : IsHom B C j)
    (hb : Function.Bijective (i.coprod j)) :
    ∃ (π : (Fin C.m → k) →ₗ[k] (Fin A.m → k)) (π' : (Fin C.m → k) →ₗ[k] (Fin B.m → k)),
      IsHom C A π ∧ IsHom C B π' ∧ (∀ x, π (i x) = x) ∧ (∀ x, π (j x) = 0) ∧ (∀ x, π' (i x) = 0) ∧
      (∀ x, π' (j x) = x) ∧ ∀ x, i (π x) + j (π' x) = x := by
  let e := LinearEquiv.ofBijective _ hb
  have h1 : ∀ x y, e.symm (i x + j y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; simp [e]
  have h2 : ∀ x, i (e.symm x).1 + j (e.symm x).2 = x := fun x => by
    exact e.apply_symm_apply x
  have h3 : ∀ g x, e.symm (C.ρ g x) = (A.ρ g (e.symm x).1, B.ρ g (e.symm x).2) := fun g x => by
    rw [← h1, hi, hj, ← map_add (f := _), h2]
  refine ⟨LinearMap.fst k _ _ ∘ₗ e.symm.toLinearMap, LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap,
    fun g x => ?_, fun g x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => h2 x⟩
  · simp [h3]
  · simp [h3]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]

variable {l n : ℕ} {R : RingPG k l}

theorem map_comp_apply (F : DFun R n G) {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} {h : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C) (hf : IsHom A B f) (hg : IsHom B C g)
    (hh : ∀ x, g (f x) = h x) (i : ZMod n) (x : Vc k A.m) :
    F.map B C g i (F.map A B f i x) = F.map A C h i x := by
  have : h = g ∘ₗ f := LinearMap.ext fun x => (hh x).symm
  rw [this, F.map_comp A B C f g hA hB hC hf hg]; rfl

theorem map_zero' (F : DFun R n G) {A B : Ob k G} (hA : F.Obj A) (hB : F.Obj B) (i : ZMod n) (x : Vc k A.m) :
    F.map A B 0 i x = 0 := by
  have := F.map_smul A B 0 0 hA hB (fun g x => by simp) i x
  simpa using this

theorem model_sup : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N N' : Lats k n A.m), M.Model A N → M.Model A N' → M.Model A (fun i => N i ⊔ N' i) := by
  intro k G _ _ l n _ _ _ R F r Dt M A N N' hN hN'
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨B', Nb', A₂, j', p', hB', hj', hji', hp', hps', rfl⟩ := hN'
  obtain ⟨C, i, i', hi, hi', hb, hC⟩ := M.base_sum B Nb B' Nb' hB hB'
  obtain ⟨π, π', hπ, hπ', e1, e2, e3, e4, -⟩ := exists_proj hi hi' hb
  obtain ⟨S, a, a', ha, ha', hab⟩ := exists_sum A₁ A₂
  obtain ⟨q, q', hq, hq', d1, d2, d3, d4, d5⟩ := exists_proj ha ha' hab
  have oB := M.base_obj _ _ hB
  have oB' := M.base_obj _ _ hB'
  have oC := M.base_obj _ _ hC
  have o1 := F.obj_sub _ _ _ hj hji oB
  have o2 := F.obj_sub _ _ _ hj' hji' oB'
  have oS := F.obj_sum _ _ _ _ _ ha ha' hab.2 o1 o2
  have oA := F.obj_quot _ _ _ hp hps o1
  have hJ : IsHom S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') :=
    isHom_add (isHom_comp (isHom_comp hq hj) hi) (isHom_comp (isHom_comp hq' hj') hi')
  have hP : IsHom S A (p ∘ₗ q + p' ∘ₗ q') := isHom_add (isHom_comp hq hp) (isHom_comp hq' hp')
  refine ⟨C, _, S, _, _, hC, hJ, ?_, hP, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg π hx
    have h2 := congrArg π' hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add (f := _), e1, e2, e3, e4, map_zero, add_zero,
      zero_add] at h1 h2
    have h1' : q x = 0 := hji (by simpa using h1)
    have h2' : q' x = 0 := hji' (by simpa using h2)
    rw [← d5 x, h1', h2']; simp
  · intro y
    obtain ⟨x, rfl⟩ := hps y
    exact ⟨a x, by simp [d1, d3]⟩
  · funext t
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₁ S a t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₁ S a t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i ∘ₗ j) o1 oS oC ha hJ (fun x => by simp [d1, d3]),
            ← map_comp_apply F o1 oB oC hj hi (fun _ => rfl)]
          exact Submodule.mem_sup_left ⟨_, hy, rfl⟩
        · exact map_comp_apply F o1 oS oA ha hP (fun x => by simp [d1, d3]) t y
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₂ S a' t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₂ S a' t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i' ∘ₗ j') o2 oS oC ha' hJ (fun x => by simp [d2, d4]),
            ← map_comp_apply F o2 oB' oC hj' hi' (fun _ => rfl)]
          exact Submodule.mem_sup_right ⟨_, hy, rfl⟩
        · exact map_comp_apply F o2 oS oA ha' hP (fun x => by simp [d2, d4]) t y
    · rintro _ ⟨s, hs, rfl⟩
      change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t s ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t at hs
      obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, h⟩ := Submodule.mem_sup.1 hs
      change F.map B C i t u + F.map B' C i' t u' = _ at h
      have h1 := congrArg (F.map C B π t) h
      have h2 := congrArg (F.map C B' π' t) h
      rw [map_add (f := _), map_comp_apply F (h := LinearMap.id) oB oC oB hi hπ e1,
        map_comp_apply F (h := 0) oB' oC oB hi' hπ e2, F.map_id B oB, map_zero' F oB' oB,
        map_comp_apply F (h := j ∘ₗ q) oS oC oB hJ hπ (fun x => by simp [e1, e2]),
        ← map_comp_apply F oS o1 oB hq hj (fun _ => rfl), add_zero, LinearMap.id_apply] at h1
      rw [map_add (f := _), map_comp_apply F (h := LinearMap.id) oB' oC oB' hi' hπ' e4,
        map_comp_apply F (h := 0) oB oC oB' hi hπ' e3, F.map_id B' oB', map_zero' F oB oB',
        map_comp_apply F (h := j' ∘ₗ q') oS oC oB' hJ hπ' (fun x => by simp [e3, e4]),
        ← map_comp_apply F oS o2 oB' hq' hj' (fun _ => rfl), zero_add, LinearMap.id_apply] at h2
      change F.map S A _ t s ∈ _
      rw [F.map_add S A _ _ oS oA (isHom_comp hq hp) (isHom_comp hq' hp'),
        ← map_comp_apply F oS o1 oA hq hp (fun _ => rfl), ← map_comp_apply F oS o2 oA hq' hp' (fun _ => rfl)]
      refine Submodule.add_mem_sup ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
      · change F.map A₁ B j t _ ∈ Nb t
        rw [← h1]; exact hu
      · change F.map A₂ B' j' t _ ∈ Nb' t
        rw [← h2]; exact hu'

end GlobalTheory.Models.SupModel
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem exact_of_finrank_add {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (h0 : p ∘ₗ f = 0)
    (hd : Module.finrank K V = Module.finrank K U + Module.finrank K W) : Function.Exact f p := by
  rw [LinearMap.exact_iff]
  have hle : LinearMap.range f ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h0, LinearMap.zero_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at hrn
  have hrf := LinearMap.finrank_range_of_inj hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem finrank_add_of_exact {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (he : Function.Exact f p) :
    Module.finrank K V = Module.finrank K U + Module.finrank K W := by
  rw [LinearMap.exact_iff] at he
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [he, LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.finrank_range_of_inj hf] at hrn
  omega

theorem DFun.map_exact_middle {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k))
    (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hB : F.Obj B) (hf : IsHom A B f) (hp : IsHom B C p)
    (hi : Function.Injective f) (hs : Function.Surjective p) (he : Function.Exact f p) (i : ZMod n) :
    Function.Exact (F.map A B f i) (F.map B C p i) := by
  have hA : F.Obj A := F.obj_sub A B f hf hi hB
  have hC : F.Obj C := F.obj_quot B C p hp hs hB
  have hd := finrank_add_of_exact f p hi hs he
  simp only [Module.finrank_fin_fun] at hd
  have hpf : p ∘ₗ f = 0 := LinearMap.ext fun x => he.apply_apply_eq_zero x
  have h0hom : IsHom A C (0 : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) := fun g x => by simp
  have hcomp : F.map B C p i ∘ₗ F.map A B f i = 0 := by
    rw [← F.map_comp A B C f p hA hB hC hf hp i, hpf]
    refine LinearMap.ext fun x => ?_
    have h := F.map_smul A C 0 0 hA hC h0hom i x
    simpa using h
  refine exact_of_finrank_add (F.map A B f i) (F.map B C p i) (F.map_inj A B f hA hB hf hi i)
    (F.map_surj B C p hB hC hp hs i) hcomp ?_
  simp only [Vc, Module.finrank_fin_fun]
  exact hd

end GlobalTheory.Models
end

section

noncomputable section
namespace GlobalTheory.Models.EPolyModel
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem map_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a) (g' : Vc k b →ₗ[k] Vc k b)
    (h : ∀ x, φ (g x) = g' (φ x)) (x : Vc k a) : φ (nab g x) = nab g' (φ x) := by
  rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, h]

theorem map_aeval_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (f : Polynomial k) (x : Vc k a) :
    φ (Polynomial.aeval (nab g) f x) = Polynomial.aeval (nab g') f (φ x) := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact φ.map_smul_of_tower c x
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval (nab g')), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, map_nab φ g g' h]

theorem comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ)
    (hN : EPoly g' N s) : EPoly g (N.comap (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, fun x hx => ?_⟩
  have h1 := hN (φ x) hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  change φ _ ∈ N
  rwa [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem map {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k a)) (s : ℤ)
    (hN : EPoly g N s) : EPoly g' (N.map (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hN x hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  refine ⟨_, h1, ?_⟩
  change φ _ = _ • nab g' (Polynomial.aeval (nab g') f (φ x))
  rw [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem model_ePoly : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T3 l →
    ∀ (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i, Dt.ty i = LType.Bd →
      EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h3 A N hN i hi
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have oB := M.base_obj B Nb hB
  have o1 := F.obj_sub A₁ B j hj hji oB
  have oA := F.obj_quot A₁ A p hp hps o1
  exact map _ _ _ (F.map_γ A₁ A p o1 oA hp i) _ _
    (comap _ _ _ (F.map_γ A₁ B j o1 oB hj i) _ _ (M.base_e h1 h3 B Nb hB i hi))

end GlobalTheory.Models.EPolyModel
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem ModTh.model_push_of_surjective {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n A.m) (hp : IsHom A B p)
    (hs : Function.Surjective p) (hN : M.Model A N) : M.Model B (F.push A B p N) := by
  obtain ⟨C, Nb, A₁, j, q, hb, hj, hji, hq, hqs, rfl⟩ := hN
  have hC : F.Obj C := M.base_obj C Nb hb
  have h1 : F.Obj A₁ := F.obj_sub A₁ C j hj hji hC
  have hA : F.Obj A := F.obj_quot A₁ A q hq hqs h1
  have hB : F.Obj B := F.obj_quot A B p hp hs hA
  refine ⟨C, Nb, A₁, j, p ∘ₗ q, hb, hj, hji, fun g x => ?_, hs.comp hqs, ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hq g x, hp g]
  · funext i
    simp only [DFun.push]
    rw [F.map_comp A₁ A B q p h1 hA hB hq hp i, ← Submodule.map_comp]
    rfl

end GlobalTheory.Models
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.GenKernelFit

theorem aeval_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (p : Polynomial k) : ∀ y ∈ Q, Polynomial.aeval T p y ∈ Q := by
  first
  | exact @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main ..)

theorem apply_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (f : Polynomial k) (hf : f.eval 0 ≠ 0) (x : U)
    (h1 : T (Polynomial.aeval T f x) ∈ Q) (j : ℕ) (h2 : (T ^ j) x ∈ Q) : T x ∈ Q := by
  have hc : IsCoprime f Polynomial.X := by
    refine ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_).symm
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hf
  obtain ⟨a, b, hab⟩ := hc.pow_right (n := j)
  have e : (Polynomial.X : Polynomial k) =
      a * (Polynomial.X * f) + b * (Polynomial.X * Polynomial.X ^ j) := by
    linear_combination (-Polynomial.X) * hab
  have e2 : T x = Polynomial.aeval T a (T (Polynomial.aeval T f x)) + Polynomial.aeval T b (T ((T ^ j) x)) := by
    have := congrArg (fun p => Polynomial.aeval T p x) e
    simpa only [map_add (f := _), map_mul, map_pow, Polynomial.aeval_X, LinearMap.add_apply, Module.End.mul_apply]
      using this
  rw [e2]
  exact Q.add_mem (aeval_mem T Q hQ a _ h1) (aeval_mem T Q hQ b _ (hQ _ h2))

theorem nab_mem_of_ePoly : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  intro k _ l n m _ _ _ R D i N s hC hE x hx hj
  obtain ⟨f, hf, hE⟩ := hE
  obtain ⟨j, hj⟩ := hj
  exact apply_mem (nab (D.γ i)) ((sh s N).restrictScalars k)
    (GlobalTheory.PhiGam.condC_sh_and_nab_mem R (D.γ i) (D.γ_semi i) N hC s).2 f hf x (hE x hx) j hj

end GlobalTheory.GenKernelFit
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_obj_and_abc : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → F.Obj A ∧ ABC (F.D A) Dt.w Dt.wst N := by
  intro k G _ _ l n _ _ _ R F r Dt M A N h
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := h
  have oB : F.Obj B := M.base_obj B Nb hB
  have o1 : F.Obj A₁ := F.obj_sub A₁ B j hj hji oB
  have oA : F.Obj A := F.obj_quot A₁ A p hp hps o1
  obtain ⟨h1, h2, h3⟩ := M.base_abc B Nb hB
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.phiGammaModule_saturation_theorem R (F.D B) (F.D A₁) (F.map A₁ B j)
    (F.map_inj A₁ B j o1 oB hj hji) (F.map_φ A₁ B j o1 oB hj) (F.map_γ A₁ B j o1 oB hj)
    Dt.w Dt.wst Nb h1 h2 h3
  exact ⟨oA, GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective R (F.D A₁) (F.D A) (F.map A₁ A p)
    (F.map_surj A₁ A p o1 oA hp hps) (F.map_φ A₁ A p o1 oA hp) (F.map_γ A₁ A p o1 oA hp)
    Dt.w Dt.wst (F.pre A₁ B j Nb) s1 s2 s3⟩

end GlobalTheory.Models
end

section

noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.CloseTw
open GlobalTheory.PhiGam.Close

theorem main : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (h : ZMod n → ℕ) (w : ZMod n → ℤ) (N₁ N₂ : Lats k n m), (∀ i, IsLat (N₁ i)) → (∀ i, IsLat (N₂ i)) → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₁ → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₂ → ∀ i, sh (sg l h i) (N₁ i) ≤ N₂ i := by
  intro k _ l n m hl _ _ R D h w N₁ N₂ h₁ h₂ c₁ c₂ i
  classical
  have hex : ∀ i, ∃ a : ℕ, ∀ x ∈ N₁ i, vv k ^ a • x ∈ N₂ i := fun i => exists_pow (h₁ i).1 (h₂ i).2
  have hrec : ∀ i, Nat.find (hex (i - 1)) ≤ (Nat.find (hex i) + h i) / l := by
    intro i
    refine Nat.find_min' _ fun x hx => ?_
    refine key hl.out.pos R (D.φ i) (D.φ_semi i) (D.etale i) _ (h₂ _) _ x ?_
    have e1 : vv k ^ (w i) • D.φ i x ∈ N₁ i := by
      have := mem_sh_iff_smul_mem.1 ((c₁ i).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
      rwa [neg_neg] at this
    have e2 := (c₂ i).2 (mem_sh_iff_exists.2 ⟨_, Nat.find_spec (hex i) _ e1, rfl⟩)
    have hv := vv_ne_zero k
    rw [smul_smul, smul_smul, ← zpow_natCast, ← zpow_add₀ hv, ← zpow_add₀ hv] at e2
    rw [← zpow_natCast]
    convert e2 using 3
    push_cast
    ring
  have hle := le_sg hl.out.one_lt h (fun i => Nat.find (hex i)) (fun i => by
    have := hrec (i + 1)
    simp only [add_sub_cancel_right] at this
    exact (Nat.mul_le_mul_left l this).trans (Nat.mul_div_le _ _)) i
  exact sh_le fun x hx => pow_smul_mem hle (Nat.find_spec (hex i) x hx)

end GlobalTheory.PhiGam.CloseTw
end
end

section

open GlobalTheory.BI GlobalTheory.BrauerZero

theorem _root_.GlobalTheory.T.inducedClassFunction_mem_inducedDegreeOneCharDiff : ∀ {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ), f ∈ D0 E → ind E f ∈ D0 G := by
  first | exact @GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | exact GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | (intros; apply GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

theorem isoProj_mem_L : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ c v hv
  letI := Fintype.ofFinite (rootsOfUnity e K)
  have key : ∀ s : ZMod a → K, (∀ τ, ‖s τ‖ ≤ 1) → ∀ w ∈ P.L, diagScale K a ι s w ∈ P.L := by
    intro s hs w hw
    have h : diagScale K a ι s w = (fun τ => C (s τ)) • w := by
      ext τ i
      simp [diagScale_apply, Pi.smul_apply', PowerSeries.smul_eq_C_mul]
    rw [h]
    refine P.smul_tot_mem_ext (fun τ => mem_A.2 fun n => ?_) hw
    rw [coeff_C]
    split_ifs
    · exact hs τ
    · simp
  have hnd : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ e + 1 := by
      rw [TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)]
      exact dvd_pow_self l (NeZero.ne a)
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))
  have he : ‖(e : K)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_natCast_eq l, Padic.norm_natCast_eq_one_iff.2
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd), inv_one]
  have hsc : isoProj Δ c v = diagScale K a ι (fun _ => (e : K)⁻¹) (∑ ζ : rootsOfUnity e K,
      diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val)
        (Δ.act (TameGal.inertia ζ) v)) := by
    simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  rw [hsc]
  refine key _ (fun _ => he) _ (Submodule.sum_mem _ fun ζ _ => key _ (fun τ => ?_) _ ?_)
  · rw [norm_pow, norm_inv, TameGal.norm_root, inv_one, one_pow]
  · exact Δ.act_mem_ext _ le_rfl rot_A hv

end GlobalTheory.CokerL
end
