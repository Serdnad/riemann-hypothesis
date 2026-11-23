module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle027
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  first | exact @GlobalTheory.SS.ArcInf.exists_isChart | exact GlobalTheory.SS.ArcInf.exists_isChart | (intros; apply GlobalTheory.SS.ArcInf.exists_isChart <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.indep_of_special_fibres : ∀ C : Core, C.HasTests → (∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' → rPt p ≫ y = rPt p ≫ y' → ∃ (τ : C.Test y) (τ' : C.Test y'), ∀ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j → ∃ c' : Sp (kb p) ⟶ τ'.H.left, c' ≫ τ'.H.hom = rPt p ≫ spMap τ'.j ∧ c' ≫ τ'.f = c ≫ τ.f) → C.Indep := by
  intro C _ h p _ y y' hy hy' hr b hb
  obtain ⟨τ, τ', hτ⟩ := h p y y' hy hy' hr
  obtain ⟨c, hc, hcb⟩ := τ.lift b hb
  obtain ⟨c', hc', hcf⟩ := hτ (rPt p ≫ c) (by rw [Category.assoc, hc])
  have := τ'.smooth
  have : Smooth τ'.H.hom := SmoothOfRelativeDimension.smooth C.g τ'.H.hom
  obtain ⟨d, hd, hdr⟩ := GlobalTheory.T.exists_classical_lift_of_smooth' p _ _ τ'.H.hom (spMap τ'.j) c' hc'
  refine ⟨d ≫ τ'.f, ?_, ?_⟩
  · rw [Category.assoc, τ'.f_over, ← Category.assoc, hd, τ'.fac]
  · rw [← Category.assoc, hdr, hcf, Category.assoc, hcb]

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_irr_and_weakNeron' : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' : Over (Sp K)), (∀ (M : Model R A) (N : Model R A'), M.Irr → N.Irr → (M.prod N).Irr) ∧ ∀ (I I' : Type) (M : I → Model R A) (N : I' → Model R A'), WeakNeron M → WeakNeron N → WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  first | exact @GlobalTheory.SS.prod_irr_and_weakNeron | exact GlobalTheory.SS.prod_irr_and_weakNeron | (intros; apply GlobalTheory.SS.prod_irr_and_weakNeron <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.strictModel_translates_twist_compatible : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ a b : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → GenIso M M (transl b).hom → Compat (M.twist (transl a)) (M.twist (transl b)) := by
  first | exact @GlobalTheory.SS.compat_twist_transl | exact GlobalTheory.SS.compat_twist_transl | (intros; apply GlobalTheory.SS.compat_twist_transl <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) := by
  first | exact @GlobalTheory.SS.exists_maxUnramified_frobenius_tame | exact GlobalTheory.SS.exists_maxUnramified_frobenius_tame | (intros; apply GlobalTheory.SS.exists_maxUnramified_frobenius_tame <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothThickenings

theorem mem_smoothLocus {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (I : Ideal V) (hI : I ≠ ⊤)
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V I e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW' : IsAffineOpen W := hW
  have hWle : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  set ψ := f.appLE ⊤ W hWle with hψ
  set φ : CommRingCat.of V ⟶ Γ(X, W) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ ψ with hφ
  let : Algebra V Γ(X, W) := φ.hom.toAlgebra
  have hjf : hW'.fromSpec ≫ f = Spec.map φ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hW' hWle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, hφ, Spec.map_comp]
  have : Algebra.FiniteType V Γ(X, W) := by
    have h1 : ψ.hom.FiniteType := f.finiteType_appLE (isAffineOpen_top _) hW' hWle
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2
    exact h1.comp h2
  set p := hW'.primeIdealOf ⟨x, hxW⟩
  have hpx : hW'.fromSpec p = x := hW'.fromSpec_primeIdealOf ⟨x, hxW⟩
  have hcomap : p.asIdeal.comap (algebraMap V Γ(X, W)) = IsLocalRing.maximalIdeal V := by
    have h3 : (Spec.map φ) p = IsLocalRing.closedPoint V := by
      rw [← hjf]
      exact (congrArg f hpx).trans hx
    exact congrArg PrimeSpectrum.asIdeal h3
  have hsm : ∀ e : ℕ, Algebra.Smooth (V ⧸ I ^ (e + 1))
      (TensorProduct V (V ⧸ I ^ (e + 1)) Γ(X, W)) := by
    intro e
    have hg : thick V I e = Spec.map (CommRingCat.ofHom (algebraMap V (V ⧸ I ^ (e + 1)))) := by
      unfold thick
      rw [Ideal.Quotient.algebraMap_eq]
    have := h e
    have h3 : Smooth (pullback.snd (Spec.map φ) (thick V I e)) := by
      rw [← hjf, ← pullbackRightPullbackFstIso_inv_snd_snd f (thick V I e) hW'.fromSpec]
      have hA : IsOpenImmersion (pullback.snd hW'.fromSpec (pullback.fst f (thick V I e))) :=
        inferInstance
      exact MorphismProperty.comp_mem @Smooth _ _ inferInstance
        (MorphismProperty.comp_mem @Smooth _ _ inferInstance this)
    have h4 : Smooth ((pullbackSpecIso V Γ(X, W) (V ⧸ I ^ (e + 1))).inv ≫ pullback.snd _ _) := by
      have : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V Γ(X, W))))
          (Spec.map (CommRingCat.ofHom (algebraMap V (V ⧸ I ^ (e + 1)))))) := by
        rw [← hg]
        exact h3
      infer_instance
    rw [pullbackSpecIso_inv_snd] at h4
    have h5 := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h4
    have h6 := RingHom.Smooth.propertyIsLocal.respectsIso.1 _
      (Algebra.TensorProduct.comm V Γ(X, W) (V ⧸ I ^ (e + 1))).toRingEquiv h5
    have heq : algebraMap (V ⧸ I ^ (e + 1)) (TensorProduct V (V ⧸ I ^ (e + 1)) Γ(X, W)) =
        (Algebra.TensorProduct.comm V Γ(X, W) (V ⧸ I ^ (e + 1))).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : (V ⧸ I ^ (e + 1)) →ₐ[V] _).toRingHom := by
      ext t
      simp
    rw [← RingHom.smooth_algebraMap, heq]
    exact h6
  have hq : Algebra.IsSmoothAt V p.asIdeal := GlobalTheory.T.isSmoothAt_of_smooth_mod_ideal_powers V I hI Γ(X, W) hsm p.asIdeal hcomap
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) W hW' hWle hxW]
  let : Algebra Γ(Spec (CommRingCat.of V), ⊤) Γ(X, W) := ψ.hom.toAlgebra
  show Algebra.FormallySmooth Γ(Spec (CommRingCat.of V), ⊤) (Localization.AtPrime p.asIdeal)
  rw [← RingHom.formallySmooth_algebraMap]
  rw [Algebra.IsSmoothAt, ← RingHom.formallySmooth_algebraMap] at hq
  have e2 := RingHom.FormallySmooth.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv hq
  convert e2 using 1
  ext a
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply Γ(Spec (CommRingCat.of V), ⊤) Γ(X, W) (Localization.AtPrime p.asIdeal),
    IsScalarTower.algebraMap_apply V Γ(X, W) (Localization.AtPrime p.asIdeal)]
  congr 1
  show ψ a = φ ((Scheme.ΓSpecIso (CommRingCat.of V)).hom a)
  rw [hφ, CommRingCat.comp_apply, Iso.hom_inv_id_apply]

theorem smooth_of_smooth_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (B : Over (Spec (CommRingCat.of R))), IsProper B.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, Smooth (Y e).hom) → Smooth B.hom := by
  intro R _ _ _ I hI B _ Y b hpb hY
  have : LocallyOfFinitePresentation B.hom := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B.hom.smoothLocus := by
    by_contra! H
    exact hne (eq_top_iff.mpr fun z _ => H z)
  have hcl : IsClosed (B.hom '' (B.hom.smoothLocus : Set B.left)ᶜ) :=
    B.hom.isClosedMap _ B.hom.smoothLocus.2.isClosed_compl
  obtain ⟨z', hz', hz'c⟩ :=
    (IsLocalRing.specializes_closedPoint (B.hom z)).mem_closed hcl ⟨z, hz, rfl⟩
  apply hz'
  refine mem_smoothLocus I hI B.hom (fun e => ?_) z' hz'c
  rw [← (hpb e).isoPullback_inv_snd]
  have := hY e
  infer_instance

end GlobalTheory.SmoothThickenings
end
