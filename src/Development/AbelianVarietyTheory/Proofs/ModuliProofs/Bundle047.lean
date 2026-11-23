module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

namespace QuotientDescent

variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}

noncomputable def up (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (Over.pullback π).obj T ⟶ G :=
  Over.homMk (H.lift (pullback.fst T.hom π ≫ z.left) (pullback.snd T.hom π)
    (by rw [Category.assoc, Over.w, pullback.condition])) (H.lift_snd ..)

theorem up_left (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (up H z).left ≫ φ = pullback.fst T.hom π ≫ z.left := H.lift_fst ..

theorem hom_ext (H : IsPullback φ G.hom G'.hom π) {T : Over X} {x y : T ⟶ G}
    (h : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (H.hom_ext h ((Over.w x).trans (Over.w y).symm))

theorem up_comp (H : IsPullback φ G.hom G'.hom π) {T T' : Over X'} (u : T' ⟶ T) (z : T ⟶ G') :
    up H (u ≫ z) = (Over.pullback π).map u ≫ up H z := by
  refine hom_ext H ?_
  have A : ((Over.pullback π).map u).left ≫ pullback.fst T.hom π = pullback.fst T'.hom π ≫ u.left :=
    pullback.lift_fst _ _ _
  rw [up_left, Over.comp_left, Over.comp_left, Category.assoc, up_left, ← Category.assoc,
    ← Category.assoc, A]

variable {Γ : Type} [Group Γ] [Finite Γ] {ρ : Γ →* Aut X} {τ : Γ →* Aut G.left}

theorem up_injective (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over X'}
    (hT : Flat T.hom) : Function.Injective (up H : (T ⟶ G') → _) := fun x y e ↦ by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  refine Over.OverMorphism.ext (hq'.hom_ext ?_)
  rw [← up_left H, ← up_left H, e]

def Equivariant (ρ : Γ →* Aut X) (τ : Γ →* Aut G.left) {T : Over X'}
    (w : (Over.pullback π).obj T ⟶ G) : Prop :=
  ∀ g (s : pullback T.hom π ⟶ pullback T.hom π), s ≫ pullback.fst T.hom π = pullback.fst T.hom π →
    s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).asIso.hom →
    s ≫ w.left = w.left ≫ (τ g).asIso.hom

theorem Equivariant.exists_up (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hτ : ∀ g, (τ g).asIso.hom ≫ φ = φ) {T : Over X'} (hT : Flat T.hom)
    {w : (Over.pullback π).obj T ⟶ G} (hw : Equivariant ρ τ w) : ∃ z : T ⟶ G', up H z = w := by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  obtain ⟨z, hz⟩ := hq'.exists_comp_eq (w.left ≫ φ) fun g ↦ by
    rw [← Category.assoc, hw g _ (hσ g).1 (hσ g).2, Category.assoc, hτ]
  refine ⟨Over.homMk z (hq'.hom_ext ?_), hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

omit [Finite Γ] in
theorem equivariant_up (H : IsPullback φ G.hom G'.hom π) (hτ : ∀ g, (τ g).asIso.hom ≫ φ = φ)
    (hτ' : ∀ g, (τ g).asIso.hom ≫ G.hom = G.hom ≫ (ρ g).asIso.hom) {T : Over X'} (z : T ⟶ G') :
    Equivariant ρ τ (up H z) := fun g s h₁ h₂ ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hτ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, hτ', e, h₂, reassoc_of% e]

noncomputable def equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).asIso.hom (τ g).asIso.hom)
    (T : Over X') : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ (g : Γ) (s : pullback T.hom π ⟶ pullback T.hom π)
    (_ : s ≫ pullback.fst T.hom π = pullback.fst T.hom π)
    (h : s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).asIso.hom),
    (preHom (Over.homMk s h)).eqLocus (pushHom (hτ g) ((Over.pullback π).obj T))

omit [Finite Γ] in
theorem mem_equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).asIso.hom (τ g).asIso.hom)
    {T : Over X'} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariantSubgroup hτ T ↔ Equivariant ρ τ w := by
  simp only [equivariantSubgroup, Subgroup.mem_iInf]
  exact ⟨fun h g s h₁ h₂ ↦ congrArg (fun z ↦ z.left) (h g s h₁ h₂),
    fun h g s h₁ h₂ ↦ Over.OverMorphism.ext (h g s h₁ h₂)⟩

end QuotientDescent

open QuotientDescent

theorem quotient_descend_grpObj :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (O : Type) [CommRing O] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (a : OAct O G), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).asIso.hom ≫ φ = φ ∧ IsGrpPullback G G (ρ g).asIso.hom (τ g).asIso.hom ∧ ∀ c, (a.act c).left ≫ (τ g).asIso.hom = (τ g).asIso.hom ≫ (a.act c).left) → ∃ (_ : GrpObj G') (_ : IsCommMonObj G') (a' : OAct O G'), IsGrpPullback G G' π φ ∧ ∀ c, (a.act c).left ≫ φ = φ ≫ (a'.act c).left := by
  intro Γ _ _ O _ X X' ρ π G _ _ G' φ τ a ⟨h₁, h₂, h₃⟩ H hG' hτ
  have hq : IsAffineQuotient ρ π :=
    ⟨h₂, h₁, fun V ↦ (h₃ V).1, fun V s hs ↦ (h₃ V).2 s fun g _ ↦ (hs g).2⟩
  have hp (g) := (hτ g).2.1
  have f₀ : Flat (𝟙_ (Over X')).hom := inferInstanceAs (Flat (𝟙 X'))
  have f₂ {A B : Over X'} (hA : Flat A.hom) (hB : Flat B.hom) : Flat (A ⊗ B).hom :=
    inferInstanceAs (Flat (pullback.fst A.hom B.hom ≫ A.hom))
  have inj {T : Over X'} (hT : Flat T.hom) {x y : T ⟶ G'} (e : up H x = up H y) : x = y :=
    up_injective hq H hT e
  have ex {T : Over X'} (hT : Flat T.hom) {w : (Over.pullback π).obj T ⟶ G}
      (hw : w ∈ equivariantSubgroup hp T) : ∃ z : T ⟶ G', up H z = w :=
    ((mem_equivariantSubgroup hp).mp hw).exists_up hq H (fun g ↦ (hτ g).1) hT
  have mem {T : Over X'} (z : T ⟶ G') : up H z ∈ equivariantSubgroup hp T :=
    (mem_equivariantSubgroup hp).mpr (equivariant_up H (fun g ↦ (hτ g).1) (fun g ↦ (hp g).1.w) z)
  obtain ⟨m, hm⟩ := ex (f₂ hG' hG') (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := ex f₀ (one_mem _)
  obtain ⟨i, hi⟩ := ex hG' (inv_mem (mem (𝟙 G')))
  have hb (c : O) : ∃ z : G' ⟶ G', up H z = up H (𝟙 G') ≫ a.act c :=
    ex hG' ((mem_equivariantSubgroup hp).mpr fun g s k₁ k₂ ↦ by
      rw [Over.comp_left, Category.assoc, (hτ g).2.2,
        reassoc_of% ((mem_equivariantSubgroup hp).mp (mem (𝟙 G')) g s k₁ k₂)])
  choose b hb using hb
  have hm' {T : Over X'} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over X'} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  have hb' {T : Over X'} (u : T ⟶ G') (c : O) : up H (u ≫ b c) = up H u ≫ a.act c := by
    rw [up_comp, hb, ← Category.assoc, ← up_comp, Category.comp_id]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (f₂ f₀ hG') (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (f₂ hG' f₀) (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (f₂ (f₂ hG' hG') hG') (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over X'} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have : IsCommMonObj G' := ⟨inj (f₂ hG' hG') (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  let a' : OAct O G' :=
    { act := b
      hom c := by
        have := a.hom c
        refine ⟨inj f₀ ?_, inj (f₂ hG' hG') ?_⟩
        · rw [hb']
          change up H e ≫ _ = up H e
          rw [he, MonObj.one_comp]
        · rw [hb']
          change up H m ≫ _ = up H (_ ≫ m)
          rw [hm', hm, tensorHom_fst, tensorHom_snd, hb', hb', MonObj.mul_comp]
      one := inj hG' (by rw [hb, a.one, Category.comp_id])
      mul c d := inj hG' (by rw [hb', hb, hb, a.mul, Category.assoc])
      add c d := inj hG' (by rw [hmul, hb, hb, hb, a.add, MonObj.comp_mul]) }
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, this, a', ⟨H, fun T x y x₀ y₀ hx hy ↦ ?_⟩, fun c ↦ ?_⟩
  · obtain ⟨s, hs⟩ := sec (T := T)
    have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
      QuotientDescent.hom_ext H ((k y₀).trans hy)]
  · obtain ⟨s, hs⟩ := sec (T := G)
    have k (z : Over.mk (G.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    let u : Over.mk (G.hom ≫ π) ⟶ G' := Over.homMk φ H.w
    have hu : s ≫ up H u = 𝟙 G := QuotientDescent.hom_ext H ((k u).trans (Category.id_comp _).symm)
    have := k (u ≫ b c)
    rwa [hb', reassoc_of% hu] at this

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ActSpread

variable {O : Type} [CommRing O] {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem act_zero {T : Scheme.{0}} {G : Over T} [GrpObj G] (i : OAct O G) : i.act 0 = 1 := by
  have h : i.act 0 * i.act 0 = i.act 0 * 1 := by rw [← i.add, add_zero, _root_.mul_one]
  exact mul_left_cancel h

theorem act_neg {T : Scheme.{0}} {G : Over T} [GrpObj G] (i : OAct O G) (x : O) : i.act (-x) = (i.act x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← i.add, neg_add_cancel, act_zero]

section
variable {T : Scheme.{0}} {x : T ⟶ S} {G : Over T} [GrpObj G] {φ : G.left ⟶ A.left}

theorem compat_iff (hG : IsGrpPullback G A x φ) (u : G ⟶ G) (f : A ⟶ A) :
    u.left ≫ φ = φ ≫ f.left ↔
      pushHom hG G u = (Over.homMk φ hG.1.w : Over.mk (G.hom ≫ x) ⟶ A) ≫ f := by
  have hp : (pushHom hG G u).left = u.left ≫ φ := by
    rfl
  constructor
  · intro h
    ext1
    rw [hp, h]
    simp
  · intro h
    have h' := congrArg Over.Hom.left h
    rw [hp] at h'
    simpa using h'

theorem compat_one (hG : IsGrpPullback G A x φ) : (1 : G ⟶ G).left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  rw [compat_iff hG, map_one]
  simp

theorem compat_mul (hG : IsGrpPullback G A x φ) {u v : G ⟶ G} {f g : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) (hg : v.left ≫ φ = φ ≫ g.left) : (u * v).left ≫ φ = φ ≫ (f * g).left := by
  rw [compat_iff hG] at hf hg ⊢
  rw [map_mul, hf, hg, comp_mul]

theorem compat_inv (hG : IsGrpPullback G A x φ) {u : G ⟶ G} {f : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) : (u⁻¹).left ≫ φ = φ ≫ (f⁻¹).left := by
  rw [compat_iff hG] at hf ⊢
  rw [map_inv, hf, GrpObj.comp_inv]

omit [GrpObj A] [GrpObj G] in
theorem compat_comp {u v : G ⟶ G} {f g : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) (hg : v.left ≫ φ = φ ≫ g.left) : (u ≫ v).left ≫ φ = φ ≫ (f ≫ g).left := by
  simp only [Over.comp_left, Category.assoc, hg]
  rw [reassoc_of% hf]

omit [GrpObj A] [GrpObj G] in
theorem compat_id : (𝟙 G : G ⟶ G).left ≫ φ = φ ≫ (𝟙 A : A ⟶ A).left := by
  simp

end

theorem exists_universal [IsCommMonObj A] {J : Type} (a : J → O) (act₀ : J → (A ⟶ A))
    (hcl : Subring.closure (Set.range a) = ⊤) (hh : ∀ j, IsMonHom (act₀ j)) (c : O) :
    ∃ f : A ⟶ A, IsMonHom f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left)
      (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) →
      (act.act c).left ≫ φ = φ ≫ f.left := by
  have m1 : IsMonHom (1 : A ⟶ A) := by
    rw [Hom.one_def]; infer_instance
  have m2 : ∀ f g : A ⟶ A, IsMonHom f → IsMonHom g → IsMonHom (f * g) := fun f g _ _ => by
    rw [Hom.mul_def]; infer_instance
  have hc : c ∈ Subring.closure (Set.range a) := hcl ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact ⟨act₀ j, hh j, fun _ _ _ _ _ _ _ h => h j⟩
  | zero =>
    refine ⟨1, m1, fun _ _ _ _ _ act hG _ => ?_⟩
    rw [act_zero]
    exact compat_one hG
  | one =>
    refine ⟨𝟙 A, inferInstance, fun _ _ _ _ _ act _ _ => ?_⟩
    rw [act.one]
    exact compat_id
  | add y z _ _ hy hz =>
    obtain ⟨f, hf, Hf⟩ := hy
    obtain ⟨g, hg, Hg⟩ := hz
    refine ⟨f * g, m2 f g hf hg, fun T x G _ φ act hG h => ?_⟩
    rw [act.add]
    exact compat_mul hG (Hf T x G φ act hG h) (Hg T x G φ act hG h)
  | neg y _ hy =>
    obtain ⟨f, hf, Hf⟩ := hy
    refine ⟨f⁻¹, inferInstance, fun T x G _ φ act hG h => ?_⟩
    rw [act_neg]
    exact compat_inv hG (Hf T x G φ act hG h)
  | mul y z _ _ hy hz =>
    obtain ⟨f, hf, Hf⟩ := hy
    obtain ⟨g, hg, Hg⟩ := hz
    refine ⟨f ≫ g, inferInstance, fun T x G _ φ act hG h => ?_⟩
    rw [act.mul]
    exact compat_comp (Hf T x G φ act hG h) (Hg T x G φ act hG h)


omit [GrpObj A] in
theorem ext_of_dense [IsReduced S] [Smooth A.hom] [IsSeparated A.hom] (f g : A ⟶ A) (D : Set S) (hD : Dense D)
    (H : ∀ p ∈ D, ∃ (T P : Scheme.{0}) (x : T ⟶ S) (q : P ⟶ T) (φ : P ⟶ A.left), p ∈ Set.range x ∧
      IsPullback φ q A.hom x ∧ φ ≫ f.left = φ ≫ g.left) : f = g := by
  have hred : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : f.left ≫ A.hom = g.left ≫ A.hom := by rw [Over.w f, Over.w g]
  obtain ⟨-, -, H3⟩ := GlobalTheory.dense_fibres_ext A.left S A.hom D hD
  have hin : ∀ y : A.left, A.hom y ∈ D → pullback.lift f.left g.left hw y ∈ Set.range (pullback.diagonal A.hom) := by
    intro y hy
    obtain ⟨T, P, x, q, φ, ⟨t, ht⟩, hpb, hφ⟩ := H _ hy
    have key : φ ≫ pullback.lift f.left g.left hw = (φ ≫ f.left) ≫ pullback.diagonal A.hom := by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
          pullback.diagonal_snd, Category.comp_id, hφ]
    have hy' : y ∈ Set.range (pullback.fst A.hom x) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    obtain ⟨z, hz⟩ := hy'
    have hinv : hpb.isoPullback.inv ≫ φ = pullback.fst A.hom x := by
      exact hpb.isoPullback_inv_fst
    refine ⟨(φ ≫ f.left) (hpb.isoPullback.inv z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← key, Scheme.Hom.comp_apply, ← hz, ← hinv, Scheme.Hom.comp_apply]
  obtain ⟨e, he⟩ := H3 _ _ (pullback.diagonal A.hom) (pullback.lift f.left g.left hw) hin
  have e1 := congrArg (· ≫ pullback.fst A.hom A.hom) he
  have e2 := congrArg (· ≫ pullback.snd A.hom A.hom) he
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at e1 e2
  ext1
  rw [← e1, ← e2]

end GlobalTheory.ActSpread

namespace GlobalTheory


open ActSpread in
theorem oAct_spread_of_dense_fibres : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] (act₀ : J → (A ⟶ A)), Subring.closure (Set.range a) = ⊤ → IsAbelianScheme A → (∀ j, IsMonHom (act₀ j)) → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (φ : G.left ⟶ A.left) (act : OAct O G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ ∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left} → ∃ r : OAct O A, (∀ j, r.act (a j) = act₀ j) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  intro O _ J a S _ A _ act₀ hcl hab hh hD
  obtain ⟨hcomm, hsm, hpr, -⟩ := hab
  choose F hF HF using fun c => ActSpread.exists_universal a act₀ hcl hh c
  have ext : ∀ f g : A ⟶ A, (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (G : Over (Sp K)) [GrpObj G]
      (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ →
      (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → φ ≫ f.left = φ ≫ g.left) → f = g := by
    intro f g H
    refine ActSpread.ext_of_dense f g _ hD ?_
    rintro p ⟨K, _, x, G, _, φ, act, hp, hG, hc⟩
    exact ⟨Sp K, G.left, x, G.hom, φ, hp, hG.1, H K x G φ act hG hc⟩
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, ?_, fun T x G _ φ act hG hc c => HF c T x G φ act hG hc⟩
  · refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF 1 _ x G φ act hG hc, act.one]
    exact ActSpread.compat_id
  · intro b c
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (b * c) _ x G φ act hG hc, act.mul]
    exact ActSpread.compat_comp (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)
  · intro b c
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (b + c) _ x G φ act hG hc, act.add]
    exact ActSpread.compat_mul hG (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)
  · intro j
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (a j) _ x G φ act hG hc]
    exact hc j

end GlobalTheory
end
end
