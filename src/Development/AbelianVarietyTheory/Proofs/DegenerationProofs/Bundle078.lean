module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBound
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.AbelianImage

theorem exists_lift {S : Scheme.{0}} {T N G : Over S} [IsReduced T.left] (ν : N ⟶ G)
    [IsClosedImmersion ν.left] (g : T ⟶ G) (h : Set.range g.left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  let Z : TopologicalSpace.Closeds G.left :=
    ⟨Set.range ν.left, ν.left.isClosedEmbedding.isClosed_range⟩
  have h2 : ν.left.ker ≤ g.left.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1
      (show Z ≤ ν.left.ker.support from ν.left.range_subset_ker_support)).trans
      (ReducedSubgroup.vanishingIdeal_le_ker g.left Z h)
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem relDim_le_of_isDominant {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Y) [IsDominant p] (f : Y ⟶ Spec (.of k)) {a b : ℕ}
    (ha : SmoothOfRelativeDimension a (p ≫ f)) (hb : SmoothOfRelativeDimension b f) : b ≤ a := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨A', j', hj', ⟨y, hy⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := p x) (U := ⊤) trivial
  obtain ⟨A, j, hj, ⟨z, hz⟩, hr⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := p ⁻¹ᵁ j'.opensRange) ⟨y, hy⟩
  have hrange : Set.range (j ≫ p) ⊆ Set.range j' := by
    rintro _ ⟨t, rfl⟩
    exact hr ⟨t, rfl⟩
  have hl := IsOpenImmersion.lift_fac j' (j ≫ p) hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j' (j ≫ p) hrange)
  obtain ⟨α, hα⟩ := Spec.map_surjective (j' ≫ f)
  rw [← hφ] at hl
  have : Nonempty (Spec A) := ⟨z⟩
  have : Nonempty (Spec A') := ⟨y⟩
  have : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec A') := isIntegral_of_isOpenImmersion j'
  have : IsDomain A := (affine_isIntegral_iff A).1 inferInstance
  have : IsDomain A' := (affine_isIntegral_iff A').1 inferInstance
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense ⟨_, z, rfl⟩⟩
  have : IsDominant (Spec.map φ ≫ j') := by rw [hl]; infer_instance
  have hd : IsDominant (Spec.map φ) := IsDominant.of_comp_of_isOpenImmersion _ j'
  have hinj : Function.Injective φ.hom := by
    have h1 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).1 hd.1
    rw [nilradical_eq_zero] at h1
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h1)
  letI : Algebra k A' := α.hom.toAlgebra
  letI : Algebra k A := (α ≫ φ).hom.toAlgebra
  have h1 := trdeg_eq_of_smoothOfRelativeDimension k Y f b hb A' j' hj' hα.symm
  have h2 := trdeg_eq_of_smoothOfRelativeDimension k X (p ≫ f) a ha A j hj (by
    rw [← Category.assoc, ← hl, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  have h3 := trdeg_le_of_injective (R := k) (A := A') (A' := A) ⟨φ.hom, fun _ => rfl⟩ hinj
  rw [h1, h2] at h3
  exact_mod_cast h3

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] [BraidedCategory 𝒞]

theorem isCommMonObj_of_mono {N G : 𝒞} [MonObj N] [MonObj G] [IsCommMonObj G] (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] : IsCommMonObj N := by
  refine ⟨?_⟩
  rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]


omit [BraidedCategory 𝒞] in
theorem isMonHom_of_comp_mono {M N G : 𝒞} [MonObj M] [MonObj N] [MonObj G] (l : M ⟶ N) (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] [IsMonHom (l ≫ ν)] : IsMonHom l := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end Cat


open RationalPoint in
theorem exists_image : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ ψ : B ⟶ G, IsMonHom ψ → ∃ (B' : Over (Sp k)) (_ : GrpObj B') (ν : B' ⟶ G) (π : B ⟶ B'), IsAbelianScheme B' ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ π ≫ ν = ψ ∧ (∀ F : G ⟶ G, IsMonHom F → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), ∃ y : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ψ ≫ F = y ≫ ψ) → ∃ F' : B' ⟶ B', IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ a, SmoothOfRelativeDimension a B.hom → ∃ a', a' ≤ a ∧ SmoothOfRelativeDimension a' B'.hom := by
  intro k _ _ G _ hG B _ hB ψ hψ
  obtain ⟨hc, hs, hsep, -, -⟩ := hG
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : IsProper (ψ.left ≫ G.hom) := by rw [Over.w ψ]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have hZ : IsClosed (Set.range ψ.left) := ψ.left.isClosedMap.isClosed_range
  let φ : (𝟙_ (Over (Sp k)) ⟶ B) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  have hC : ∀ x, x ∈ φ.range ↔ Set.range x.left ⊆ Set.range ψ.left := fun x => by
    rw [range_left_subset_iff, ← Set.image_univ, pt_mem_image_iff ψ isClosed_univ]
    simp only [Set.mem_univ, true_and]
    rfl
  obtain ⟨N, _, ν, hν, hcl, hsm, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k G
    inferInstance φ.range _ hZ hC
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have : IsIntegral B.left := isIntegral_of_smooth_field_of_connectedSpace B.hom
  obtain ⟨π, hπ⟩ := exists_lift ν ψ hr.ge
  have : Surjective π.left := ⟨fun y => by
    obtain ⟨x, hx⟩ := hr.le ⟨y, rfl⟩
    refine ⟨x, ν.left.isClosedEmbedding.injective ?_⟩
    rw [← hx, ← hπ]
    rfl⟩
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have : ConnectedSpace N.left := π.left.surjective.connectedSpace π.left.continuous
  have : IsIntegral N.left := isIntegral_of_smooth_field_of_connectedSpace N.hom
  have hw : π.left ≫ N.hom = B.hom := Over.w π
  have : IsSeparated N.hom := by rw [← Over.w ν]; infer_instance
  have : UniversallyClosed (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed N.hom := UniversallyClosed.of_comp_surjective π.left N.hom
  have : GeometricallyConnected (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have hN : IsAbelianScheme N := ⟨isCommMonObj_of_mono ν, hsm, ⟨⟩,
    geometricallyConnected_of_surjective π.left N.hom⟩
  refine ⟨N, inferInstance, ν, π, hN, hν, hcl, hπ, fun F hF h => ?_, fun a ha => ?_⟩
  · have h1 : Set.range (ψ ≫ F).left ⊆ Set.range ψ.left :=
      ReducedSubgroup.range_subset_of_points (ψ ≫ F) hZ fun x => by
        obtain ⟨y, hy⟩ := h x
        exact (hC _).1 ⟨y, hy.symm⟩
    obtain ⟨F', hF'⟩ := exists_lift ν (ν ≫ F) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := hr.le ⟨t, rfl⟩
      refine hr.ge (h1 ⟨x, ?_⟩)
      change F.left (ψ.left x) = F.left (ν.left t)
      rw [hx])
    have : IsMonHom (F' ≫ ν) := by rw [hF']; infer_instance
    exact ⟨F', isMonHom_of_comp_mono F' ν, hF'⟩
  · obtain ⟨b, hb⟩ := AbelianDim.exists_relDim k N hN
    exact ⟨b, relDim_le_of_isDominant π.left N.hom (hw ▸ ha) hb, hb⟩

end GlobalTheory.AbelianImage
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_sectionHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (a : T.left ⟶ S) (ha : a = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') →* (Over.mk a ⟶ G), (∀ x, (ρ x).left = x.left ≫ φ) ∧ Function.Surjective ρ := by
  subst ha
  refine ⟨pushHom h T, fun _ => rfl, fun c => ?_⟩
  exact ⟨Over.homMk (h.1.lift c.left T.hom (Over.w c)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem eSec_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    eSec G' ≫ φ = (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_fac_residue (V K : Type) [CommRing V] [IsLocalRing V] [Field K] (r : Sp K ⟶ Sp V)
    (hr : Set.range r = {IsLocalRing.closedPoint V}) :
    ∃ s : Sp K ⟶ Sp (IsLocalRing.ResidueField V), s ≫ spMap (IsLocalRing.residue V) = r := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective r
  have h : PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint V := by
    have : (Spec.map ψ) (IsLocalRing.closedPoint K) ∈ Set.range (Spec.map ψ) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  let ψ' : V →+* K := ψ.hom
  have : IsLocalHom ψ' := (IsLocalRing.isLocalHom_iff_comap_closedPoint ψ').2 h
  refine ⟨spMap (IsLocalRing.ResidueField.lift ψ'), ?_⟩
  rw [← Spec.map_comp]
  congr 1

theorem Core.Test.exists_isGt_fibre {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (K : Type) [Field K] (r : Sp K ⟶ Sp τ.V) (hr : Set.range r = {IsLocalRing.closedPoint τ.V}) :
    ∃ (G₁ : Over (Sp K)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (E : SplitExt (Sp K)) (φ : G₁.left ⟶ τ.H.left),
      E.IsGt G₁ ∧ IsGrpPullback G₁ τ.H r φ := by
  obtain ⟨s, rfl⟩ := exists_fac_residue τ.V K r hr
  obtain ⟨S, hS⟩ := τ.split
  obtain ⟨E, -, -, -, -, hE⟩ := gtBaseChange _ _ s S _ hS
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact ⟨_, _, Functor.isCommMonObj_obj, E, _, hE,
    (isGrpPullback_pullback _ s).comp (isGrpPullback_pullback τ.H _)⟩

theorem Core.Test.eSec_comp_f {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) :
    (eSec τ.H ≫ τ.f : Sp τ.V ⟶ C.G.toScheme) = τ.y₀ ≫ C.e := by
  have := C.proper
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  have : IsDominant (Out.jK τ.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective τ.V _)]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated C.GG.hom ?_ (Out.jK τ.V) ?_
  · have h₁ : (eSec τ.H ≫ τ.H.hom : Sp τ.V ⟶ Sp τ.V) = 𝟙 _ := Over.w η[τ.H]
    have h₂ : C.e ≫ C.GG.hom = 𝟙 _ := C.e_sec
    rw [Category.assoc, Category.assoc, τ.f_over, h₂, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.y₀) h₁).trans (Category.id_comp _))
  · have h₁ := @eSec_comp_of_isGrpPullback _ _ _ _ (_) (_) _ _ τ.φ_cart
    have h₂ := eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (Out.jK τ.V))
    rw [← reassoc_of% τ.yK_fac, C.e_zero]
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.a) h₁) |>.trans (Category.assoc _ _ _))
    rw [τ.φ_f]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) h₂.symm).trans (Category.assoc _ _ _))

theorem Core.fibLaw_of_testCart : ∀ C : Core, C.TestCart → C.FibLaw := by
  intro C hC p _ y y' τ τ' K _ _ r r' hr hr' hy c d c' d' hc hd
  obtain ⟨G₁, _, _, E₁, φ₁, g₁, h₁⟩ := τ.exists_isGt_fibre K r hr
  obtain ⟨G₂, _, _, E₂, φ₂, g₂, h₂⟩ := τ'.exists_isGt_fibre K r' hr'
  have P₁ := h₁.1.paste_horiz (hC p y τ)
  have P₂ := h₂.1.paste_horiz (hC p y' τ')
  let i : G₁ ⟶ G₂ := Over.homMk (P₂.lift (φ₁ ≫ τ.f) G₁.hom (by rw [P₁.w, hy])) (P₂.lift_snd _ _ _)
  have hi : i.left ≫ φ₂ ≫ τ'.f = φ₁ ≫ τ.f := P₂.lift_fst _ _ _
  have u₁ : η[G₁].left ≫ φ₁ ≫ τ.f = (r ≫ τ.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) (eSec_comp_of_isGrpPullback h₁)).trans
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) τ.eSec_comp_f)))
  have u₂ : η[G₂].left ≫ φ₂ ≫ τ'.f = (r' ≫ τ'.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ'.f) (eSec_comp_of_isGrpPullback h₂)).trans
      ((Category.assoc _ _ _).trans (congrArg (r' ≫ ·) τ'.eSec_comp_f)))
  have hone : η[G₁] ≫ i = η[G₂] := by
    apply Over.OverMorphism.ext
    apply P₂.hom_ext
    · rw [Over.comp_left, Category.assoc, hi, u₁, u₂]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.e) hy).trans (Category.assoc _ _ _))
    · rw [Over.w, Over.w]
  have := isMonHom_of_isGt_of_one K E₁ E₂ G₁ G₂ g₁ g₂ i hone
  obtain ⟨ρ₁, l₁, s₁⟩ := exists_sectionHom h₁ (Over.mk (𝟙 _)) r (Category.id_comp _).symm
  obtain ⟨ρ₂, l₂, -⟩ := exists_sectionHom h₂ (Over.mk (𝟙 _)) r' (Category.id_comp _).symm
  have key : ∀ x, (ρ₁ x).left ≫ τ.f = (ρ₂ (x ≫ i)).left ≫ τ'.f := fun x => by
    rw [l₁, l₂, Over.comp_left, Category.assoc, Category.assoc, Category.assoc, hi]
  have inj : ∀ (x) (z : Over.mk r' ⟶ τ'.H), (ρ₁ x).left ≫ τ.f = z.left ≫ τ'.f → z = ρ₂ (x ≫ i) := fun x z hz => by
    apply Over.OverMorphism.ext
    apply (hC p y' τ').hom_ext
    · exact hz.symm.trans (key x)
    · rw [Over.w, Over.w]
  obtain ⟨c, rfl⟩ := s₁ c
  obtain ⟨d, rfl⟩ := s₁ d
  obtain rfl := inj c c' hc
  obtain rfl := inj d d' hd
  constructor
  · rw [← map_mul, ← map_mul, ← MonObj.mul_comp]
    exact key _
  · rw [← map_inv, ← map_inv, ← GrpObj.inv_comp]
    exact key _

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_classical_point_lifting_residue_point : ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens), (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime], (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧ (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  first | exact @GlobalTheory.exists_integral_point_lifting_residue_point | exact GlobalTheory.exists_integral_point_lifting_residue_point | (intros; apply GlobalTheory.exists_integral_point_lifting_residue_point <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_over_subfield_of_le {Ω : Type} [Field Ω] {K L : Subfield Ω} (h : K ≤ L)
    (hK : Module.Finite K Ω) : Module.Finite L Ω := by
  letI : Algebra K L := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K L Ω

theorem exists_normal_proj_hasDiv_family (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (J : Type) [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (B : Type) [Finite B] (JJ : B → Type) [∀ b, Finite (JJ b)] (tt : ∀ b, JJ b → Ω)
    (htt : ∀ b, ∃ k, tt b k ≠ 0) :
    ∃ M : RatModel o Ω, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z ∧ IsProjOver M.s ∧ M.HasDiv t ∧ ∀ b, M.HasDiv (tt b) := by
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype (∀ b, JJ b) := Fintype.ofFinite _
  choose q₀ hq₀ using htt
  have hP : (∏ b, tt b (q₀ b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hq₀ b
  obtain ⟨i₀, hi₀⟩ := ht
  obtain ⟨M, hM, hp⟩ := GlobalTheory.ZH.exists_isNm_isProjOver o Ω (ArithBase.inj (o := o) (Ω := Ω))
    (J × ∀ b, JJ b) (fun q => t q.1 * ∏ b, tt b (q.2 b)) ⟨(i₀, q₀), mul_ne_zero hi₀ hP⟩
    (finite_over_subfield_of_le (Subfield.closure_mono (Set.union_subset_union_right _ (by
      rintro _ ⟨i, j, rfl⟩
      exact ⟨(i, q₀), (j, q₀), (mul_div_mul_right _ _ hP).symm⟩))) hfin)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M J t
  have h2 : M.HasDiv t ∧ M.HasDiv (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) := by
    refine ⟨fun z => ?_, fun z => ?_⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨i, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).1⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨q, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).2⟩
  exact ⟨M, (GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ _).1 hM, hp, h2.1, (h.2.2 B JJ tt).1 h2.2⟩

theorem exists_admissible_affine_model_dividing_tuple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ ∧ IsAffineOpen U₀ ∧ M.HasDiv t₀ := by
  intro o Ω _ _ _ _ S J₀ _ t₀ ht₀ hfin
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  haveI : NeZero S.N := ⟨hN⟩
  haveI : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (mul_ne_zero hr hN)⟩
  haveI : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
  haveI : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T =>
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨i₀, hi₀⟩ := ht₀
  obtain ⟨M, hn, hp, hd, hF⟩ := exists_normal_proj_hasDiv_family o Ω (S.Gam × J₀)
    (fun q => S.th q.1 * t₀ q.2) ⟨(x₀, i₀), mul_ne_zero hx₀ hi₀⟩ hfin
    {b : Σ T : AddSubgroup S.Gam, T →+ ZMod S.N // S.FF b.1 b.2 ≠ 0}
    (fun b => S.J × (b.1.1 → ZMod ((S.r * S.N) ^ 2))) (fun b => S.FF b.1.1 b.1.2)
    (fun b => Function.ne_iff.1 b.2)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ S.th
  have hth : M.HasDiv S.th := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨x, ((h.2.1 _ t₀ x i z).1 hi).1⟩
  have ht : M.HasDiv t₀ := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨i, ((h.2.1 _ t₀ x i z).1 hi).2⟩
  have hA : ((fun x : Ω => x⁻¹) '' (Set.range S.th ∪ {x : Ω | ∃ T c k, x = S.FF T c k})).Finite :=
    ((Set.finite_range _).union (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.1).image _
  obtain ⟨U₀, a, -, hne, haff, -, -, hR, hsub⟩ := GlobalTheory.ZH.exists_affineOpen_ringOn_eq_adjoin_inv o Ω M S.R _
    S.fg S.frac hA ⊤ ⟨genericPoint M.Z, trivial⟩
  refine ⟨M, U₀, ⟨⟨hn, hp, hth, hne, fun x hx => ?_, fun x _ => hsub ⟨_, Or.inl ⟨x, rfl⟩, rfl⟩,
    fun T c k _ _ => hsub ⟨_, Or.inr ⟨T, c, k, rfl⟩, rfl⟩⟩, fun T c _ h0 => hF ⟨⟨T, c⟩, h0⟩⟩, haff, ht⟩
  rw [hR]
  exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.isIntegral_of_weightZeroCoordinate_dominates : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (a : Sp (PadicAlgCl p) ⟶ G.left) (w : J → PadicAlgCl p), a ≫ G.hom = gPt p ≫ spMap j → Crd H σ a w → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a := by
  first | exact @GlobalTheory.ZH.Mod.integral_of_weight_zero_dominates | exact GlobalTheory.ZH.Mod.integral_of_weight_zero_dominates | (intros; apply GlobalTheory.ZH.Mod.integral_of_weight_zero_dominates <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.maximal_minors_dual_thetaTest_lattice_bound : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → ∀ (n : ℕ) (ρ₀ : ℝ) (g : Fin n → S.J → PadicAlgCl p), 0 < ρ₀ → (∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range g) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ ρ₀) → (∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J) ∧ ((∃ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ = ρ₀ ^ Fintype.card S.J) ↔ S.perp τ.yy.ker = ⊥) := by
  first | exact @GlobalTheory.ZH.minors_dual_testLattice | exact GlobalTheory.ZH.minors_dual_testLattice | (intros; apply GlobalTheory.ZH.minors_dual_testLattice <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.span_rows_classZero_eq_invariant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  first | exact @GlobalTheory.ZH.span_rows_class_zero | exact GlobalTheory.ZH.span_rows_class_zero | (intros; apply GlobalTheory.ZH.span_rows_class_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.seriesProportional_add_iota_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (a : u.PtC) (g h g' : GtPtF u.D.toPre (PadicAlgCl p)) (y : u.D.toPre.X), 1 ≤ k → GtPtF.IsIota y h → GtPtF.IsAdd g h g' → (u.ParAt k a g ↔ u.ParAt k a g') := by
  first | exact @GlobalTheory.ZH.IotaShift.parAt_add_iota | exact GlobalTheory.ZH.IotaShift.parAt_add_iota | (intros; apply GlobalTheory.ZH.IotaShift.parAt_add_iota <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.specialFibre_torsion_eq_reductions : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ((S.r * S.N : ℕ) : kb p) ≠ 0 ∧ (∀ x : md.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ a ∈ l.yy.ker, ∃ (c : Sp (OO p) ⟶ u.G.left) (a' : u.PtC), c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = u.toG a' ∧ u.toA a' = spMap y₀ ≫ (ρ.pt a).left ∧ rPt p ≫ c = x.left ≫ md.r) ∧ ∀ a ∈ l.yy.ker, ∃ (c : Sp (OO p) ⟶ u.G.left) (a' : u.PtC) (x : md.Φ.Pt), c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = u.toG a' ∧ u.toA a' = spMap y₀ ≫ (ρ.pt a).left ∧ rPt p ≫ c = x.left ≫ md.r ∧ x ^ (S.r * S.N) = 1 := by
  first | exact @GlobalTheory.ZH.special_torsion_eq_reduction | exact GlobalTheory.ZH.special_torsion_eq_reduction | (intros; apply GlobalTheory.ZH.special_torsion_eq_reduction <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.testField_finite_over_padic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), CharZero u.V ∧ IsLocalHom u.j ∧ Function.Injective u.j ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ (K : Set (PadicAlgCl p)) = Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  first | exact @GlobalTheory.ZH.FieldOfTest.fractionRing_finite_over_padic | exact GlobalTheory.ZH.FieldOfTest.fractionRing_finite_over_padic | (intros; apply GlobalTheory.ZH.FieldOfTest.fractionRing_finite_over_padic <;> assumption)
end
