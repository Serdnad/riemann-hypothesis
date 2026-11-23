module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

variable {R' : Type} [CommRing R'] {I : Ideal R'} {S : Scheme.{0}}

def crysAct (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) : O →+* Module.End R' (Crys κ t A) :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; push κ t (a.act x)
      map_one' := haveI := a.hom 1; (push_congr κ t a.one).trans (push_id κ t)
      map_mul' x y := by
        haveI := a.hom
        exact (push_congr κ t (a.mul x y)).trans (push_comp κ t _ _) }
    fun x y ↦ by
      haveI := a.hom
      haveI : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (push_congr κ t (a.add x y)).trans (push_mul κ t _ _)

theorem crysAct_apply (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) (x : O) (h : Crys κ t A) :
    crysAct κ t a x h = (haveI := a.hom x; push κ t (a.act x) h) := rfl

@[reducible] def tensorModOf {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) : Module (C ⊗[ℤ] B) H :=
  Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId C (Module.End C H)) ρ.toIntAlgHom
    fun r _ ↦ Algebra.commutes r _).toRingHom

theorem tensorModOf_tmul {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) (r : C) (x : B) (h : H) :
    (letI := tensorModOf ρ; (r ⊗ₜ[ℤ] x : C ⊗[ℤ] B) • h) = r • ρ x h := rfl

end GlobalTheory.HTSummand
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UnifPull

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X}
  {φ : G'.left ⟶ G.left}

def push (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : Over.mk t ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = t
    rw [Category.assoc, hw, ← Category.assoc, Over.w x, ← ht]
    rfl)

theorem push_left (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : (push hw ht x).left = x.left ≫ φ := rfl

def pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : Over.mk t' ⟶ G' :=
  Over.homMk (H.lift x.left t' ((Over.w x).trans ht.symm)) (H.lift_snd _ _ _)

theorem push_pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : push H.w ht (pull H ht x) = x :=
  Over.OverMorphism.ext (H.lift_fst _ _ _)

theorem push_injective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Injective (push H.w ht) := fun x y h =>
  Over.OverMorphism.ext (H.hom_ext (congrArg (fun u => u.left) h) (by rw [Over.w x, Over.w y]))

theorem push_surjective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Surjective (push H.w ht) := fun x => ⟨_, push_pull H ht x⟩

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') (x y : Over.mk t' ⟶ G') :
    push hφ.1.w (t := t' ≫ f) rfl (x * y) = push hφ.1.w rfl x * push hφ.1.w rfl y :=
  Over.OverMorphism.ext (hφ.2 (Over.mk t') x y (push hφ.1.w rfl x) (push hφ.1.w rfl y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') :
    push hφ.1.w (t := t' ≫ f) rfl (1 : Over.mk t' ⟶ G') = 1 := by
  have h := push_mul hφ t' 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem push_comp (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) (x : Over.mk t' ⟶ G') :
    push hw ht (x ≫ a') = push hw ht x ≫ a :=
  Over.OverMorphism.ext (by
    show (x ≫ a').left ≫ φ = (push hw ht x ≫ a).left
    rw [Over.comp_left, Over.comp_left, push_left, Category.assoc, ha, Category.assoc])

theorem isDerivAt0_iff_comp (H : IsPullback φ G'.hom G.hom f) {g : ℕ} {y' : Sp ℂ ⟶ X'}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ G'.left)} (he : ∀ z, e z ≫ G'.hom = y')
    (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) (w : Fin g → ℂ) {v : Sp (DualNumber ℂ) ⟶ G'.left}
    (hv : v ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') :
    IsDerivAt0 e w v ↔ IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨fun h => FibreDeriv.isDerivAt0_comp h φ, fun h => ?_⟩
  have H₁ := (IsPullback.of_hasPullback G'.hom y').paste_horiz H
  let e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ pullback G'.hom y') :=
    fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp])
  let v₁ : Sp (DualNumber ℂ) ⟶ pullback G'.hom y' := pullback.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv
  have h1 : ∀ z, e₁ z ≫ pullback.fst _ _ = e z := fun z => pullback.lift_fst _ _ _
  have hv1 : v₁ ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have hf1 : (fun z => e₁ z ≫ pullback.fst G'.hom y' ≫ φ) = fun z => e z ≫ φ :=
    funext fun z => by rw [← Category.assoc, h1]
  have key := FibreDeriv.isDerivAt0_of_isPullback H₁ (e := e₁) (fun z => pullback.lift_snd _ _ _)
    (by rw [hf1]; exact hol) (pullback.lift_snd _ _ _) (by rw [hf1, ← Category.assoc, hv1]; exact h)
  have := FibreDeriv.isDerivAt0_comp key (pullback.fst _ _)
  rw [hv1] at this
  simpa only [h1] using this

theorem spMap_fst_alg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem isExp_iff (hφ : IsGrpPullback G' G f φ) {g : ℕ} (y' : Sp ℂ ⟶ X') (e : (Fin g → ℂ) → (Over.mk y' ⟶ G')) :
    IsExp y' e ↔ IsExp (y' ≫ f) (fun z => push hφ.1.w rfl (e z)) := by
  have H := hφ.1
  have hpe : ∀ z, (push H.w (t := y' ≫ f) rfl (e z)).left = (e z).left ≫ φ := fun z => rfl
  have hes : ∀ z, (e z).left ≫ G'.hom = y' := fun z => Over.w (e z)
  have hol : IsHolTo Set.univ (fun z => (e z).left) ↔ IsHolTo Set.univ (fun z => (e z).left ≫ φ) :=
    ⟨fun h => HolFibre.isHolTo_comp h φ, fun h => HolFibre.isHolTo_of_isPullback H h
      (by simp only [hes]; exact HolFibre.isHolTo_const isOpen_univ y')⟩
  have ht : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (y' ≫ f) :=
    Category.assoc _ _ _
  let pE : (epsPt y' ⟶ G') → (epsPt (y' ≫ f) ⟶ G) := push H.w ht
  have pEi : Function.Injective pE := push_injective H ht
  have pEs : Function.Surjective pE := push_surjective H ht
  have hd : IsHolTo Set.univ (fun z => (e z).left ≫ φ) → ∀ w (v : epsPt y' ⟶ G'),
      IsDerivAt0 (fun z => (e z).left) w v.left ↔ IsDerivAt0 (fun z => (push H.w (t := y' ≫ f) rfl (e z)).left) w (pE v).left :=
    fun h w v => isDerivAt0_iff_comp H hes h w (Over.w v)
  have hbase : ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (pE v).left =
      (push H.w (t := y' ≫ f) rfl (e 0)).left ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := by
    intro v
    refine ⟨fun h => H.hom_ext (by rw [Category.assoc]; exact h) ?_, fun h => ?_⟩
    · rw [Category.assoc, Over.w v, hes]
      show spMap _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y' = y'
      rw [← Category.assoc, spMap_fst_alg, Category.id_comp]
    · show spMap _ ≫ v.left ≫ φ = (e 0).left ≫ φ
      rw [← Category.assoc, h]
  have hinj : Function.Injective (push H.w (t := y' ≫ f) rfl (t' := y')) := push_injective H rfl
  constructor
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' := hol.1 hh
    refine ⟨fun z w => by dsimp only; rw [hadd, push_mul hφ], (push_surjective H rfl).comp hsurj, hh', fun w => ?_,
      fun v hv => ?_⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      refine ⟨pE v, (hd hh' w v).1 hv, fun v' hv' => ?_⟩
      obtain ⟨v', rfl⟩ := pEs v'
      rw [hu v' ((hd hh' w v').2 hv')]
    · obtain ⟨v, rfl⟩ := pEs v
      obtain ⟨w, hw, hu⟩ := hd2 v ((hbase v).1 hv)
      exact ⟨w, (hd hh' w v).1 hw, fun w' hw' => hu w' ((hd hh' w' v).2 hw')⟩
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' : IsHolTo Set.univ (fun z => (e z).left ≫ φ) := hh
    refine ⟨fun z w => hinj (by have h := hadd z w; dsimp only at h; rw [h, push_mul hφ]), fun x => ?_, hol.2 hh', fun w => ?_, fun v hv => ?_⟩
    · obtain ⟨z, hz⟩ := hsurj (push H.w rfl x)
      exact ⟨z, hinj hz⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      obtain ⟨v, rfl⟩ := pEs v
      exact ⟨v, (hd hh' w v).2 hv, fun v' hv' => pEi (hu _ ((hd hh' w v').1 hv'))⟩
    · obtain ⟨w, hw, hu⟩ := hd2 (pE v) ((hbase v).2 hv)
      exact ⟨w, (hd hh' w v).2 hw, fun w' hw' => hu w' ((hd hh' w' v).1 hw')⟩

end GlobalTheory.UnifPull

namespace GlobalTheory.UnifPull

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {R R' : Type} [CommRing R]
  [CommRing R'] {σ : R →+* ℂ} {σ' : R' →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {F' : Fam R' O Λ g} {N : ℕ}
  {f : F'.X ⟶ F.X} {φ : F'.A.left ⟶ F.A.left}

theorem unifAt_iff (hφ : IsGrpPullback F'.A F.A f φ) (hact : ∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left)
    (hL : LBIso F'.L (F.L.pull φ)) (heta : ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) (D' : PLat O bar)
    (t : Λ → D'.La) (P : D'.La →+ (Fin g → ℂ)) (y' : Sp ℂ ⟶ F'.X) (hy' : y' ≫ F'.s = spMap σ')
    (hy : (y' ≫ f) ≫ F.s = spMap σ) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F'.A)) :
    UnifAt F' σ' ρ N D' t P y' e' ↔ UnifAt F σ ρ N D' t P (y' ≫ f) (fun z => push hφ.1.w rfl (e' z)) := by
  have hinj : Function.Injective (push hφ.1.w (t := y' ≫ f) rfl (t' := y')) := push_injective hφ.1 rfl
  have hker : ∀ z, push hφ.1.w (t := y' ≫ f) rfl (e' z) = 1 ↔ e' z = 1 := fun z => by
    rw [← push_one hφ y']
    exact hinj.eq_iff
  have hlin : ∀ a z, e' (ρ a *ᵥ z) = e' z ≫ F'.act a ↔
      push hφ.1.w (t := y' ≫ f) rfl (e' (ρ a *ᵥ z)) = push hφ.1.w rfl (e' z) ≫ F.act a := fun a z => by
    rw [← push_comp hφ.1.w rfl (hact a)]
    exact hinj.eq_iff.symm
  have hweil : ∀ (k : ℤ) (x x' : Over.mk y' ⟶ F'.A) (c : Γ(Sp ℂ, ⊤)ˣ), Out.WeilIs F'.A F'.L k x x' c ↔
      Out.WeilIs F.A F.L k (push hφ.1.w (t := y' ≫ f) rfl x) (push hφ.1.w rfl x') c := fun k x x' c =>
    GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ F.A F'.A f φ F.L F'.L F.isLB F'.isLB hφ hL (Over.mk y') k x x' _ _ c
      rfl rfl
  have hunit : ∀ a, push hφ.1.w (t := y' ≫ f) rfl (toUnit (Over.mk y') ≫ F'.eta a) =
      toUnit (Over.mk (y' ≫ f)) ≫ F.eta a := fun a => Over.OverMorphism.ext (by
    rw [push_left, Over.comp_left, Over.comp_left, Category.assoc, heta]
    simp)
  have heta' : ∀ a x, toUnit _ ≫ F'.eta a = x ↔ toUnit _ ≫ F.eta a = push hφ.1.w (t := y' ≫ f) rfl x :=
    fun a x => by
      rw [← hunit]
      exact hinj.eq_iff.symm
  constructor
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy, hP, (isExp_iff hφ y' e').1 hE, fun z => (hker z).trans (hK z), fun a z => (hlin a z).1 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).1 (hW k a b c hk hc), fun a => (heta' a _).1 (hT a)⟩
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy', hP, (isExp_iff hφ y' e').2 hE, fun z => (hker z).symm.trans (hK z), fun a z => (hlin a z).2 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).2 (hW k a b c hk hc), fun a => (heta' a _).2 (hT a)⟩

end GlobalTheory.UnifPull


open GlobalTheory.UnifPull in
theorem GlobalTheory.unifAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  intro O _ bar g ρ R R' _ _ σ σ' Λ F F' N f φ hφ hact hL heta D' t P y' hy' hy
  refine ⟨fun e' he' => ⟨_, (unifAt_iff hφ hact hL heta D' t P y' hy' hy e').1 he', fun z => rfl⟩,
    fun e he => ⟨fun z => pull hφ.1 rfl (e z), ?_, fun z => (hφ.1.lift_fst _ _ _).symm⟩⟩
  have h : (fun z => push hφ.1.w (t := y' ≫ f) rfl (pull hφ.1 rfl (e z))) = e := funext fun z => push_pull hφ.1 rfl (e z)
  exact (unifAt_iff hφ hact hL heta D' t P y' hy' hy _).2 (by rw [h]; exact he)
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


namespace GlobalTheory.AbCoh

theorem exists_lift_of_bock_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl x hB
  have hσc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hse.1
  have hσ₀c : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hse.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hσc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip hσ₀c
  obtain ⟨f, w, hfw, hf, hw⟩ := hB
  have R1 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).1
  have R2 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).2.1
  have R3 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).2.2.1
  have S := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have B := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R' X X' φ s').1.1
  obtain ⟨c, hc, hcx⟩ := (R1 f x).1 hf
  obtain ⟨c₀, hc₀, hc₀z⟩ := (R2 w 0).1 hw
  rw [map_zero, H2.mk_eq_zero] at hc₀z
  obtain ⟨b, hb⟩ := hc₀z
  choose u hu using fun (U V : AffOp X) (a : U ⟶ V) ↦ (S V).2.2.1 (b U V a)
  have nat₀ : ∀ {V W : AffOp X} (a : V ⟶ W) (y : (OAff s).obj V),
      preα φ₀ s s₀ W (mp (OAff s) a y) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ V y) :=
    fun a y ↦ (preCoef h₀.w).naturality a y
  have hker : ∀ (U V W : AffOp X) (a : U ⟶ V) (a' : V ⟶ W), t • (w U V W a a' - d1 (OAff s) u U V W a a') = 0 := by
    intro U V W a a'
    rw [← (S W).2.2.2, map_sub, d1_apply, map_add (f := _), map_sub, nat₀, hu, hu, hu, ← hc₀, ← d1_apply, hb, sub_self]
  have hg : f - t • u ∈ Z1 (OAff s) := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, map_sub, hfw, map_smul, ← smul_sub]
    funext U V W a a'
    exact hker U V W a a'
  refine ⟨H1.mk _ ⟨f - t • u, hg⟩, B ?_⟩
  rw [R3, CoefMap.pullCohomologyOne_class, ← hcx]
  congr 1
  refine Subtype.ext ?_
  funext U V a
  rw [CoefMap.pullCocycleOne_apply, hc]
  show preα φ s s' V (f U V a - t • u U V a) = _
  rw [map_sub, ((S V).2.1 _).2 ⟨_, rfl⟩, sub_zero]

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem exists_bock : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF x
  have hc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hS.1
  have hc₀ : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hS.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback h.flip hc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback h₀.flip hc₀
  have sec := fun U ↦ GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF U
  have red := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w
  have red₀ := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have bij₀ := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R₀ X X₀ φ₀ s₀).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ ((preRes φ s').pull1 x)
  choose f hf using fun (U V : AffOp X) (a : U ⟶ V) ↦ (sec V).1 (c.1 U V a)
  have hd : ∀ (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W), preα φ s s' W (d1 (OAff s) f U V W a b) = 0 := by
    intro U V W a b
    have nat := (preCoef h.w).naturality b (f U V a)
    have cc := c.2 a b
    rw [d1_apply, map_add (f := _), map_sub, hf, hf]
    erw [nat, hf]
    rw [cc]; ring
  choose w hw using fun (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W) ↦ ((sec W).2.1 _).1 (hd U V W a b)
  have hdw : d1 (OAff s) f = t • w := by
    funext U V W a b; exact hw U V W a b
  have hw2 : ∀ ⦃U V W Y : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W) (e : W ⟶ Y),
      t • (mp (OAff s) e (w U V W a b) + w U W Y (a ≫ b) e - (w U V Y a (b ≫ e) + w V W Y b e)) = 0 := by
    intro U V W Y a b e
    have := (differential_one_mem_scaled_lattice (OAff s) f) a b e
    rw [hdw] at this
    simp only [Pi.smul_apply, map_smul] at this
    rw [smul_sub, smul_add, smul_add, this, sub_self]
  have hc0 : (fun U V W (a : U ⟶ V) (b : V ⟶ W) ↦ preα φ₀ s s₀ W (w U V W a b) : C2 (OPre φ₀ s₀)) ∈
      Z2 (OPre φ₀ s₀) := by
    intro U V W Y a b e
    have h1 := ((sec Y).2.2.2 _).2 (hw2 a b e)
    have nat := (preCoef h₀.w).naturality e (w U V W a b)
    simp only [map_add (f := _), map_sub] at h1
    erw [nat] at h1
    dsimp only
    exact sub_eq_zero.1 h1
  obtain ⟨z, hz⟩ := bij₀.2 (GlobalTheory.CatCoh.H2.mk _ ⟨_, hc0⟩)
  exact ⟨z, f, w, hdw, (red.1 f x).2 ⟨c, fun U V a ↦ (hf U V a).symm, hc⟩,
    (red₀.2.1 w z).2 ⟨⟨_, hc0⟩, fun U V W a b ↦ rfl, hz.symm⟩⟩

end GlobalTheory.AbCoh
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem tmul_of_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, pullHO1 h.w y = 0 → ∃ u : HO1 s₀, TMul h₀.w t u y := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl y hy
  have : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hse.1)
  have : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hse.2.2.1)
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have hred := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w
  have hred₀ := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have hb₀ := GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R₀ X X₀ φ₀ s₀
  have nat : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ s s' V (mp (OAff s) a b) = mp (OPre φ s') a (preα φ s s' U b) :=
    fun a b ↦ (preCoef h.w).naturality a b
  have nat₀ : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ₀ s s₀ V (mp (OAff s) a b) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U b) :=
    fun a b ↦ (preCoef h₀.w).naturality a b
  obtain ⟨c, rfl⟩ := H1.mk_surjective _ y
  have h1 : (preCoef h.w).pull1 (H1.mk _ c) = 0 := by rw [← hred.2.2.1, hy, map_zero]
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h1
  obtain ⟨g', hg'⟩ := h1
  choose g hg using fun U ↦ (hsec U).1 (g' U)
  have hk : ∀ (U V : AffOp X) (a : U ⟶ V), preα φ s s' V (c.1 U V a - d0 _ g U V a) = 0 := by
    intro U V a
    have e := congrFun (congrFun (congrFun hg' U) V) a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [map_sub, amitsur_d0_apply, map_sub, nat, hg, hg]
    exact sub_eq_zero.2 e.symm
  choose f hf using fun U V a ↦ ((hsec V).2.1 _).1 (hk U V a)
  let c' : Z1 (OAff s) := c - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
  have hc' : c'.1 = t • (f : C1 (OAff s)) := by
    funext U V a; exact hf U V a
  have hz : ∀ ⦃U V W : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W),
      t • (mp (OAff s) b (f U V a) + f V W b - f U W (a ≫ b)) = 0 := by
    intro U V W a b
    have e := c'.2 a b
    rw [hc'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [smul_sub, smul_add, e, sub_self]
  let c₀ : Z1 (OPre φ₀ s₀) := ⟨fun U V a ↦ preα φ₀ s s₀ V (f U V a), fun U V W a b ↦ by
    have e := ((hsec W).2.2.2 _).2 (hz a b)
    rw [map_sub, map_add (f := _), nat₀] at e
    exact (sub_eq_zero.1 e).symm⟩
  obtain ⟨u, hu⟩ := hb₀.1.2 (H1.mk _ c₀)
  refine ⟨u, f, c', hc', ?_, (hred₀.1 f u).2 ⟨c₀, fun _ _ _ ↦ rfl, hu.symm⟩⟩
  rw [map_sub, sub_eq_self]
  exact H1.mk_eq_zero.2 ⟨g, rfl⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ), HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  first | exact @GlobalTheory.Dieu.hasLogDeg_comp_le | exact GlobalTheory.Dieu.hasLogDeg_comp_le | (intros; apply GlobalTheory.Dieu.hasLogDeg_comp_le <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.pDivGroup_isConn_of_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  first | exact @GlobalTheory.Dieu.isConn_of_isIsog | exact GlobalTheory.Dieu.isConn_of_isIsog | (intros; apply GlobalTheory.Dieu.isConn_of_isIsog <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.chernClass_kummerClass_additive : GlobalTheory.EtC.DivisorAdditivity := by
  first | (exact @GlobalTheory.EtC.a6add_holds) | (exact GlobalTheory.EtC.a6add_holds) | (intros; apply GlobalTheory.EtC.a6add_holds  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomology_bijective_of_support_bijective : GlobalTheory.EtC.A10 := by
  first | (exact @GlobalTheory.EtC.a10) | (exact GlobalTheory.EtC.a10) | (intros; apply GlobalTheory.EtC.a10  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cup_chern_kummer_pullback_naturality : GlobalTheory.EtC.DivisorNaturality := by
  first | (exact @GlobalTheory.EtC.a6nat_holds) | (exact GlobalTheory.EtC.a6nat_holds) | (intros; apply GlobalTheory.EtC.a6nat_holds  <;> assumption)
end
