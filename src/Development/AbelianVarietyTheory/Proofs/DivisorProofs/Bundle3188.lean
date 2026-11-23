module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

theorem GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i),
    ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY := by
  intro g n F W Z i X₁
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver X₁.projM
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  exact ⟨Y, q, U₀, EE, ⟨G⟩, hO, hE, hq, hqp⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.TraitLift

theorem exists_point_finite_ext {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    (K : Type) [Field K] (y : Sp K ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap K L) ≫ y := by
  let P := pullback f y
  haveI : Nonempty (Sp K) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp K))
  obtain ⟨R, e, he, ⟨q, -⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := P) (x := p) (U := ⊤) trivial
  let g' : Spec R ⟶ Sp K := e ≫ pullback.snd f y
  haveI : LocallyOfFiniteType g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]
    infer_instance
  haveI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  letI : Algebra K (R ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  haveI hft : Algebra.FiniteType K (R ⧸ I) :=
    RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨R ⧸ I, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing _ _,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ e ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_lift_of_proper {X Y : Scheme.{0}} (f : X ⟶ Y) [IsProper f] [Surjective f]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (hV : IsCN V) (y : Sp V ⟶ Y) :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ X),
      IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ f = spMap j ≫ y := by
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  obtain ⟨L, _, _, _, x, hx⟩ :=
    exists_point_finite_ext f (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ y)
  obtain ⟨V', _, _, _, hc, _, _, _, hcomp, -, hinj, hloc, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hv : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x ≫ f = spMap (algebraMap V' L) ≫ spMap (algebraMap V V') ≫ y := by
    rw [hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hcomp]
  let S : ValuativeCommSq f := { R := V', K := L, i₁ := x, i₂ := spMap (algebraMap V V') ≫ y, commSq := ⟨hsq⟩ }
  obtain ⟨l, -, hl⟩ := (hv S).some.default
  exact ⟨V', inferInstance, inferInstance, inferInstance, algebraMap V V', l,
    ⟨inferInstance, inferInstance, hc, charZero_of_injective_ringHom hinj⟩, hinj, hloc, hl⟩

theorem surjective_of_isHom_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {f : Y.Z ⟶ M.Z}
    (hf : M.IsHom Y (AlgHom.id o Ω) f) [IsProper f] : Surjective f := by
  have h : Y.pt ≫ f = M.pt := by
    rw [hf]
    exact (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  haveI : IsDominant (Y.pt ≫ f) := h ▸ inferInstance
  haveI : IsDominant f := IsDominant.of_comp Y.pt f
  infer_instance

theorem exists_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  intro g n F W Z i X₁ z₁ Y πY h V _ _ _ _ ev _ hV
  obtain ⟨U₀, EE, -, -, -, hf, hp⟩ := h
  haveI := surjective_of_isHom_id hf
  obtain ⟨V', _, _, _, j, ξ, h1, h2, h3, h4⟩ := exists_lift_of_proper πY V hV (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, j, ξ, h1, h2, h3, ?_⟩
  rw [h4, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep.TraitLift
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_cell_section : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  intro E _ _ _ H D X _ _ _ y n N hn hN Z Z' h hker hsurj
  haveI := D.proj
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hN
    omega
  let mulN : X →ₗ[𝓞 E] X := N • LinearMap.id
  have hinj : Function.Injective mulN := by
    intro u v huv
    have h1 : N • u = N • v := by simpa [mulN] using huv
    have h2 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast h3) hN0
    · exact sub_eq_zero.1 h3
  let q : D.La →ₗ[𝓞 E] D.La := LinearMap.id - Z'.subtype ∘ₗ h.proj
  have hqa : ∀ a, q a = a - (h.proj a : D.La) := fun a => rfl
  have hq : ∀ a, q a ∈ perp D Z := fun a => by rw [hqa]; exact h.sub_proj_mem a
  have hrange : ∀ a, (y ∘ₗ q) a ∈ LinearMap.range mulN := fun a => by
    obtain ⟨e, he⟩ := (hker (q a)).2 ⟨q a, hq a, 0, by simp⟩
    exact ⟨e, by simp [mulN, he]⟩
  let ε : D.La →ₗ[𝓞 E] X :=
    (LinearEquiv.ofInjective mulN hinj).symm.toLinearMap ∘ₗ (y ∘ₗ q).codRestrict _ hrange
  have hε : ∀ a, N • ε a = y (q a) := by
    intro a
    have h2 := congrArg Subtype.val ((LinearEquiv.ofInjective mulN hinj).apply_symm_apply ⟨(y ∘ₗ q) a, hrange a⟩)
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let muln : X →ₗ[𝓞 E] X := n • LinearMap.id
  let S : Submodule (𝓞 E) X := LinearMap.range muln
  let g : Z' →ₗ[𝓞 E] X ⧸ S := S.mkQ ∘ₗ y ∘ₗ Z'.subtype
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := S.mkQ_surjective x
    obtain ⟨b, hb, e, he⟩ := hsurj x
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply, he]
    rw [Submodule.Quotient.eq]
    exact ⟨e, by simp [mulN, muln]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g (S.mkQ ∘ₗ ε) hg
  have hs' : ∀ a, ∃ e, y (s a) = ε a + n • e := by
    intro a
    have h1 := LinearMap.congr_fun hs a
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply] at h1
    rw [Submodule.Quotient.eq] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨e, ?_⟩
    have he' : n • e = y (s a) - ε a := by simpa [muln] using he
    rw [he']
    abel
  refine ⟨Z'.subtype ∘ₗ h.proj + N • (Z'.subtype ∘ₗ s ∘ₗ q), fun a => ?_, fun b hb => ?_, fun a => ?_, fun a => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact add_mem (h.proj a).2 (Z'.nsmul_mem (s (q a)).2 N)
  · have hqb : q b = 0 := by rw [hqa, h.proj_of_mem hb, sub_self]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, hqb,
      map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero]
    exact h.proj_of_mem hb
  · obtain ⟨e, he⟩ := hs' (q a)
    refine ⟨N • e, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add (f := _),
      map_nsmul]
    have hy : y (q a) = y a - y (h.proj a) := by rw [hqa, map_sub]
    have hqq : q (q a) = q a := by rw [hqa (q a), h.proj_of_perp (hq a), sub_zero]
    rw [he, smul_add, hε, hqq, hy, smul_comm N n e]
    abel
  · refine ⟨(h.proj a : D.La) - a, ?_, s (q a), ?_⟩
    · have := neg_mem (h.sub_proj_mem a)
      rwa [neg_sub] at this
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      abel

end GlobalTheory.LowFilt
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumTau

theorem prod_subsets_two {M : Type} [CommMonoid M] (F : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{0, 1}⟩ := by
  have h : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, _root_.mul_assoc, _root_.mul_assoc]

def unitAt {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm f z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (f ≫ f₁)) (J₂ (f ≫ f₂)), J f))

theorem unitAt_of {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f g : Z ⟶ X) (j : L.ι) (j₁ : L₁.ι) (j₂ : L₂.ι) (hg : g = f) (h : J f = j)
    (h₁ : J₁ (f ≫ f₁) = j₁) (h₂ : J₂ (f ≫ f₂) = j₂) :
    gm g z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, j)) = unitAt w z J J₁ J₂ f := by
  subst hg h h₁ h₂
  rfl

theorem mapsAt_unitAt {Y X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} {p : Y ⟶ X} {n : ℤ}
    {a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    {b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))}
    {b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))} (h : MapsAt₂ w p n a b₁ b₂)
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} {J₁ : (Z ⟶ X₁) → L₁.ι} {J₂ : (Z ⟶ X₂) → L₂.ι}
    (hJ : Good L z J) (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    val b₁ r z J₁ * val b₂ r z J₂ = unitAt w z J J₁ J₂ (r ≫ p) ^ n * val a r z J :=
  (GlobalTheory.MumProd.mapsAt₂_val _ _ _ _ _ _ _ _ _ _ w p n a b₁ b₂ h r z J J₁ J₂ hJ hJ₁ hJ₂).trans
    (congrArg (· ^ n * val a r z J) (unitAt_of w z J J₁ J₂ _ _ _ _ _ rfl rfl
      (by rw [Category.assoc]) (by rw [Category.assoc])))

theorem val_tau {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) (a b : D.toPre.X)
    {z : (TK R).left} {J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} (hJ : Good D.toPre.P.L z J) :
    val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.psi (a + b)) (𝟙 _) z J * (val (D.toPre.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.toPre.psi b) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ := by
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre a b).choose_spec.2 _ (𝟙 _) z J hJ).trans ?_
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

section Psum

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Over S} (x : Fin 2 → (T ⟶ G))

theorem psum_empty : psum G x ∅ = toUnit T ≫ η[G] := rfl

theorem psum_zero : psum G x {0} = x 0 := by
  show lift (x 0) (toUnit T ≫ η[G]) ≫ μ[G] = x 0
  exact lift_comp_one_right _ _

theorem psum_one : psum G x {1} = x 1 := by
  show lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G] = x 1
  exact lift_comp_one_right _ _

theorem psum_pair : psum G x {0, 1} = padd G (x 0) (x 1) := by
  show padd G (x 0) (lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G]) = _
  rw [lift_comp_one_right]

theorem comp_padd' {T' : Over S} (g : T' ⟶ T) (a b : T ⟶ G) : g ≫ padd G a b = padd G (g ≫ a) (g ≫ b) := by
  unfold padd
  rw [comp_lift_assoc]

end Psum

end GlobalTheory.MumProd.SumTau

namespace GlobalTheory.MumProd


open SumTau in
theorem tau_sum_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)), wM.IsGen → (∃ b₁ b₂, MapsAt₂ wM (eSec D.toPre.P.A) 1 D.toPre.rig b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ D₁.toPre.rig ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ D₂.toPre.rig) → (∀ x, ∃ b₁ b₂, MapsAt₂ wM (D.toPre.xK x) (-1) (D.toPre.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ (D₁.toPre.psi (q₁ x)) ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ (D₂.toPre.psi (q₂ x))) → ∀ (w : LB.Iso (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L) (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L)), (∀ (Z : Scheme.{0}) (f : Z ⟶ (D₁.toPre.P.A ⊗ D.toPre.P.A).left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → D₁.toPre.P.L.ι) (jA : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι) (β : ULift.{0} (Finset (Fin 2)) → D₂.toPre.P.L.ι), f z ∈ (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L).U jC → f z ∈ (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L).U jA → (∀ I, (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left) z ∈ D₂.toPre.P.L.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card))) → ∀ (y : D₁.toPre.X) (y' : D.toPre.X) (z : (TK R).left) (J₁ : ((TK R).left ⟶ D₁.toPre.P.A.left) → D₁.toPre.P.L.ι) (J₂ : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D₁.toPre.P.L z J₁ → Good D.toPre.P.L z J₂ → val ((pol D).tau (j₁ y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ * val ((pol D₁).tau y (q₁ y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ wM _ hrig hpsi w hw y y' z J₁ J₂ hJ₁ hJ₂
  obtain ⟨J₃, hJ₃⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' D₂.toPre.P.isLB z
  have ψ : ∀ x, val (D₁.toPre.psi (q₁ x)) (𝟙 _) z J₁ * val (D₂.toPre.psi (q₂ x)) (𝟙 _) z J₃ =
      (unitAt wM z J₂ J₁ J₃ (D.toPre.xK x))⁻¹ * val (D.toPre.psi x) (𝟙 _) z J₂ := by
    intro x
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hpsi x
    have e := mapsAt_unitAt hm (𝟙 _) hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, Category.id_comp, zpow_neg_one] at e
    exact e
  have ρ : val D₁.toPre.rigK (𝟙 _) z J₁ * val D₂.toPre.rigK (𝟙 _) z J₃ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * val D.toPre.rigK (𝟙 _) z J₂ := by
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hrig
    have e := mapsAt_unitAt hm (toUnit (TK R)).left hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, zpow_one] at e
    unfold DegPre.rigK
    rw [val_pull hJ₁, val_pull hJ₃, val_pull hJ₂, Category.id_comp]
    exact e
  have z₂ := GlobalTheory.MumFam.val_psi_zero_mul_rigK R D₂.toPre D₂.tau_bimult z J₃ hJ₃
  have hc := GlobalTheory.MumProd.c_inc_fst R D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ y
  have h1 := GlobalTheory.MumProd.PsumMap.psum_comp_hom _ D.toPre.P.A D₁.toPre.P.A _ 2 p₁
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁
    (by intro i; fin_cases i <;> simp [hi₁])
  have h2 := GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ D.toPre.P.A D₂.toPre.P.A _ p₂
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by
      show (fst D₁.toPre.P.A D.toPre.P.A ≫ i₁) ≫ p₂ = _
      rw [Category.assoc, hi₂, ← Category.assoc, comp_toUnit])
  have K : adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * (unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y)))⁻¹ *
        (unitAt wM z J₂ J₁ J₃ (D.toPre.xK y'))⁻¹ * unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y + y')) := by
    have s₀ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        fst D₁.toPre.P.A D.toPre.P.A ≫ i₁ = toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [lift_fst_assoc, hc, Category.assoc]
    have s₁ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        snd D₁.toPre.P.A D.toPre.P.A = toUnit (TK R) ≫ D.toPre.c y' := lift_snd _ _
    generalize lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') = P at s₀ s₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D₁.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left) P.left
    have mA := Good.mem hJ₂ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) P.left
    have e := hw _ P.left z _ _ (fun I => J₃ (P.left ≫ (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)) mC mA
      (fun I => hJ₃ _) (fun I => by
        show J₃ _ = J₃ _
        rw [← Over.comp_left, ← Over.comp_left, h2 I.down]
        rfl)
    refine e.trans ?_
    have e' : ∀ I : ULift.{0} (Finset (Fin 2)), gm (P.left ≫ (psum D.toPre.P.A
        ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _
        (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (J₁ (P.left ≫ (psum D₁.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left))
          (J₃ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)),
          J₂ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left))) =
        unitAt wM z J₂ J₁ J₃ (P ≫ psum D.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left := fun I =>
      unitAt_of wM z J₂ J₁ J₃ _ _ _ _ _ rfl rfl
        (by rw [← h1 I.down, Over.comp_left, Over.comp_left, Category.assoc])
        (by rw [Over.comp_left, Category.assoc])
    refine (Finset.prod_congr rfl fun I _ => congrArg (· ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e' I)).trans ?_
    rw [prod_subsets_two]
    have t₀ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] ∅ =
        toUnit (TK R) ≫ η[D.toPre.P.A] := by
      rw [psum_empty, ← Category.assoc, comp_toUnit]
    have t₁ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [psum_zero]; exact s₀
    have t₂ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {1} =
        toUnit (TK R) ≫ D.toPre.c y' := by
      rw [SumTau.psum_one]; exact s₁
    have t₃ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0, 1} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y + y') := by
      rw [psum_pair, D.toPre.c_add, comp_padd', comp_padd']
      exact congrArg₂ (padd D.toPre.P.A) s₀ s₁
    have c₀ : ((-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card)) = 1 := by decide
    have c₁ : ((-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card)) = -1 := by decide
    have c₂ : ((-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card)) = -1 := by decide
    have c₃ : ((-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card)) = 1 := by decide
    simp only []
    rw [t₀, t₁, t₂, t₃, c₀, c₁, c₂, c₃, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
  have ψa := ψ (j₁ y)
  have ψb := ψ y'
  have ψab := ψ (j₁ y + y')
  rw [hj₁, hj₂] at ψa
  rw [map_add (f := _), map_add (f := _), hj₁, hj₂, zero_add] at ψab
  rw [K, val_tau D _ _ hJ₂, val_tau D₁ _ _ hJ₁, ← inv_mul_eq_iff_eq_mul.2 ψa, ← inv_mul_eq_iff_eq_mul.2 ψb,
    ← inv_mul_eq_iff_eq_mul.2 ψab, ← inv_mul_eq_iff_eq_mul.2 ρ, eq_inv_of_mul_eq_one_left z₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumProd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Transl

theorem pG_comp_lift_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (a : 𝟙_ (Over (Sp R)) ⟶ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R I e ≫ g.b.left) → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ g a β hβm e hβ hab h h₁ h₂
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG I e G).left = thick R I e ≫ a.left := pullback.lift_fst _ _ _
  have hh : h = (tr ae).left := by
    apply pullback.hom_ext
    · exact h₂.trans (tr_fst hae).symm
    · exact h₁.trans (Over.w (tr ae)).symm
  subst hh
  have k₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae) (𝟙 (thickObj R I e G))
  have k₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae) = toUnit _ ≫ g.b := by
    apply Over.OverMorphism.ext
    show ((thickObj R I e G).hom ≫ ae.left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ g.b.left
    rw [Category.assoc, Category.assoc]
    exact congrArg ((thickObj R I e G).hom ≫ ·) (hab _ (Over.w ae) hae)
  have k₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U₂.gt e).pG ≫ β.hom :=
    Over.OverMorphism.ext ((Category.id_comp _).trans hβ.symm)
  have k₄ : (U₂.gt e).pG ≫ (β.hom * (toUnit _ ≫ g.b)) = ((U₂.gt e).pG ≫ β.hom) * (toUnit _ ≫ g.b) := by
    rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
  rw [k₂, k₃, _root_.mul_comm (toUnit _ ≫ g.b), ← k₄] at k₁
  exact congrArg (fun q => q.left) k₁

end GlobalTheory.MumCmp.Transl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over S) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit ((k : Γ(S, ⊤))) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (M.pull (pullback.fst A.hom y)).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  first | (exact @GlobalTheory.RigTorsTriv.triv_of_geometricFibres) | (exact GlobalTheory.RigTorsTriv.triv_of_geometricFibres) | (intros; apply GlobalTheory.RigTorsTriv.triv_of_geometricFibres <;> assumption)
end
