module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle724
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.globalOneFormFrame_coordinates_constant : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R), (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧ ∀ w, w = ∑ i, l i w • Φ.w i := by
  first | exact @GlobalTheory.AbCoh.frame_coord | exact GlobalTheory.AbCoh.frame_coord | (intros; apply GlobalTheory.AbCoh.frame_coord <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.PrimForm

variable {R : Type} [CommRing R]

theorem pF_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : GlobForm C.hom) :
    pF g (pF f a) = pF (g ≫ f) a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.1 R R C.left B.left C.hom B.hom (RingHom.id R) f.left (ovw f) R A.left A.hom
    (RingHom.id R) g.left (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) (fun _ ↦ rfl)).2.2.1 a

theorem pF_id (A : Over (Sp R)) (a : GlobForm A.hom) : pF (𝟙 A) a = a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.2.2 R A).2.2.1 a

theorem pF_unit {A B : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (a : GlobForm A.hom) :
    pF (toUnit B ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem prim_of_axes (A : Over (Sp R)) [GrpObj A]
    (H : ∀ y : GlobForm (A ⊗ A).hom, pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 →
      pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0) : PrimF A := by
  intro x
  have e := H (pF μ[A] x - pF (fst A A) x - pF (snd A A) x) ?_ ?_
  · exact (sub_eq_zero.1 ((sub_sub _ _ _).symm.trans e))
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_right, pF_id, pF_unit,
      sub_self, sub_zero]
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_left, pF_id, pF_unit,
      sub_zero, sub_self]

end GlobalTheory.AbCoh.PrimForm
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem tMul_zero_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF y hy
  have iφ : IsClosedImmersion φ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hE.1)
  have iφ₀ : IsClosedImmersion φ₀ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hE.2.2.1)
  obtain ⟨f, c, hc, rfl, hred⟩ := hy
  obtain ⟨c₀, hc₀, hcl⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).1 f 0).1 hred
  rw [map_zero, CatCoh.H1.mk_eq_zero] at hcl
  obtain ⟨g₀, hg₀⟩ := hcl
  have hS := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF
  choose g hg using fun U => (hS U).2.2.1 (g₀ U)
  have key : ∀ U V (a : U ⟶ V), t • (f U V a - d0 (OAff s) g U V a) = 0 := by
    intro U V a
    rw [← (hS V).2.2.2]
    have hn := (preCoef h₀.w).naturality a (g U)
    have e := congrFun (congrFun (congrFun hg₀ U) V) a
    change preα φ₀ s s₀ V (mp (OAff s) a (g U)) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U (g U)) at hn
    rw [amitsur_d0_apply, hc₀] at e
    rw [amitsur_d0_apply, map_sub, map_sub, hn, hg, hg, ← e]
    ring
  refine CatCoh.H1.mk_eq_zero.2 ⟨t • g, ?_⟩
  rw [hc, map_smul]
  funext U V a
  have := key U V a
  simp only [Pi.smul_apply]
  rw [smul_sub, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.AbCoh
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  first | exact @GlobalTheory.BadCount.embReg_of_free_permuted_summands | exact GlobalTheory.BadCount.embReg_of_free_permuted_summands | (intros; apply GlobalTheory.BadCount.embReg_of_free_permuted_summands <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → UConst A.hom := by
  first | exact @GlobalTheory.AbCoh.uConst_of_isAbelianScheme | exact GlobalTheory.AbCoh.uConst_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.uConst_of_isAbelianScheme <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  first | exact @GlobalTheory.BadCount.card_mul_finrank_eig_of_free | exact GlobalTheory.BadCount.card_mul_finrank_eig_of_free | (intros; apply GlobalTheory.BadCount.card_mul_finrank_eig_of_free <;> assumption)
end

section

open Module NumberField

theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_complexEmbedding_indep : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K)) (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V) (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) → Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) → (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ), GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  first | exact @GlobalTheory.BadCount.embReg_of_baseChange | exact GlobalTheory.BadCount.embReg_of_baseChange | (intros; apply GlobalTheory.BadCount.embReg_of_baseChange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V1 V2 : Submodule K R) [FiniteDimensional K V2] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V1) → (∀ h : H, ∀ x ∈ V1, act h x ∈ V1) → (∀ h : H, ∀ x ∈ V1, x * act h u ∈ V2) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V2 := by
  first | exact @GlobalTheory.BadCount.embReg_of_groupDet | exact GlobalTheory.BadCount.embReg_of_groupDet | (intros; apply GlobalTheory.BadCount.embReg_of_groupDet <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_le_card_mul_finrank_characterSpace_baseChange : ∀ (K L Γ R W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V : Submodule K R) [FiniteDimensional K V] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ Vm, x * act h u ∈ V) → ∀ [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ lam : H →* Lˣ, finrank K Vm ≤ Nat.card H * finrank L (eig ρ' H lam) := by
  first | exact @GlobalTheory.BadCount.finrank_le_card_mul_finrank_eig_baseChange | exact GlobalTheory.BadCount.finrank_le_card_mul_finrank_eig_baseChange | (intros; apply GlobalTheory.BadCount.finrank_le_card_mul_finrank_eig_baseChange <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dOne_glob_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  intro R _ C _ F hF hH w
  obtain ⟨n, u, v, h⟩ := twoForm_eq_wsum R C F hF hH (fun T ↦ dOne R (F.obj T) (w.1 T))
    (fun T T' φ ↦ by rw [pOm_dOne, ← w.2 φ])
  exact ⟨n, u, v, fun T ↦ congrFun h T⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ ζ : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ζ T' = pOm F 2 φ (ζ T)) → ∃ (n : ℕ) (u v : Fin n → Glob1 F), ζ = wsum F u v := by
  first | exact @GlobalTheory.AbCoh.twoForm_eq_wsum | exact GlobalTheory.AbCoh.twoForm_eq_wsum | (intros; apply GlobalTheory.AbCoh.twoForm_eq_wsum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.one_sub_goodIdempotent_eq_badTupleSums : ∀ (D : D7), ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ 1 - D.ntypes.e0 = badElt D 0 (S 0) + badElt D 1 (S 1) - badElt D 0 (S 0) * badElt D 1 (S 1) := by
  first | exact @GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums | exact GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums | (intros; apply GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums <;> assumption)
end
