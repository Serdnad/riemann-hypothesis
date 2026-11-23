module

public import Development.EtaleCohomology.EtaleSheaves.Bundle030
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.EtaleCohomology.EtaleSheaves.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.EtaleCohomology.EtaleSheaves.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.SpreadingOut
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
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafDimBoundPf

theorem dim_le_of_quasiFinite (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.QuasiFinite A S] : ringKrullDim S ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A S)) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := hPQ.le
  refine lt_of_le_of_ne (fun x hx => hle hx) ?_
  intro h
  apply hPQ.ne
  have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P.asIdeal Q.asIdeal hle
    (congrArg PrimeSpectrum.asIdeal h)
  exact PrimeSpectrum.ext this

theorem dim_le_of_stdSmooth1 (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] : ringKrullDim S ≤ ringKrullDim R + 1 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := 1) R S
  let _ : Algebra (MvPolynomial (Fin 1) R) S := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin 1) R) S := hg
  have h1 := dim_le_of_quasiFinite (MvPolynomial (Fin 1) R) S
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing] at h1
  simpa using h1

theorem dim_affineOpen {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    topologicalKrullDim (V : Set X) = ringKrullDim Γ(X, V) := by
  have h1 : topologicalKrullDim (V : Set X) = topologicalKrullDim (Spec Γ(X, V)) :=
    (Scheme.homeoOfIso hV.isoSpec).isHomeomorph.topologicalKrullDim_eq
  rw [h1]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

theorem dim_affineOpen_Spec_le (A : CommRingCat.{0}) {U : (Spec A).Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(Spec A, U) ≤ ringKrullDim A := by
  rw [← dim_affineOpen hU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := A)]
  exact topologicalKrullDim_subspace_le _ _

theorem LeafDimBound_of : LateralTheory.E.LeafDescendVCut.LeafDimBound := by
  intro k _ Ω _ _ R hR D0 q hq
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := hq.exists_isStandardSmoothOfRelativeDimension x
  have : IsNoetherianRing Γ(Sp R, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Sp R, U) Γ(D0, V) := (q.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Sp R, U) Γ(D0, V) := hs
  refine ⟨(V : Set D0), V.isOpen, hx, ?_⟩
  rw [dim_affineOpen hV]
  calc ringKrullDim Γ(D0, V) ≤ ringKrullDim Γ(Sp R, U) + 1 := dim_le_of_stdSmooth1 _ _
    _ ≤ ringKrullDim R + 1 := by
      gcongr
      exact dim_affineOpen_Spec_le (CommRingCat.of R) hU

end LateralTheory.E.LeafDimBoundPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafDescendMapPf

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

abbrev J (R : Subalgebra k Ω) : Type := {S : Subalgebra k Ω // R ≤ S ∧ S.FG}

instance (R : Subalgebra k Ω) : IsDirected (J R) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, le_sup_of_le_left a.2.1, a.2.2.sup b.2.2⟩, le_sup_left (a := a.1), le_sup_right (a := a.1)⟩⟩

lemma toR_incl {R S : Subalgebra k Ω} (h : R ≤ S) : toR S ≫ incl h = toR R := by
  rw [toR, incl, toR, ← Spec.map_comp]; rfl

lemma incl_incl {R S T : Subalgebra k Ω} (h : R ≤ S) (h' : S ≤ T) :
    incl h' ≫ incl h = incl (h.trans h') := by
  rw [incl, incl, incl, ← Spec.map_comp]; rfl

lemma incl_base {R S : Subalgebra k Ω} (h : R ≤ S) :
    incl h ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
  rw [incl, ← Spec.map_comp]; rfl

lemma toR_base (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [toR, ← Spec.map_comp]; rfl

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

lemma incl_self {S : Subalgebra k Ω} (h : S ≤ S) : incl h = 𝟙 _ := by
  rw [incl, ← Spec.map_id]; rfl

variable (R : Subalgebra k Ω)

def F : J R ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

def coc : Cocone (F R) where
  pt := CommRingCat.of Ω
  ι := { app S := CommRingCat.ofHom (algebraMap S.1 Ω) }

def cocIsColimit (hR : R.FG) : IsColimit (coc R) := by
  haveI : Nonempty (J R) := ⟨⟨R, le_rfl, hR⟩⟩
  haveI : ReflectsColimitsOfShape (J R) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{0})
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : Ω)
    have hx : x ∈ R ⊔ Algebra.adjoin k {x} := le_sup_right (a := R) (Algebra.subset_adjoin rfl)
    exact ⟨⟨R ⊔ Algebra.adjoin k {x}, le_sup_left, hR.sup (by simpa using Subalgebra.fg_adjoin_finset (R := k) ({x} : Finset Ω))⟩, ⟨x, hx⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, le_sup_of_le_left i.2.1, i.2.2.sup j.2.2⟩, homOfLE (le_sup_left (a := i.1)),
      homOfLE (le_sup_right (a := i.1)), ?_⟩
    apply Subtype.ext
    exact h

def specLim (hR : R.FG) : IsLimit (Scheme.Spec.mapCone (coc R).op) :=
  isLimitOfPreserves Scheme.Spec (cocIsColimit R hR).op

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {D0 : Scheme.{0}} (q : D0 ⟶ Sp R)

abbrev D : (J R)ᵒᵖ ⥤ Scheme.{0} where
  obj S := pullback q (incl S.unop.2.1)
  map {S T} h := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ incl (leOfHom h.unop))
    (by rw [pullback.condition, Category.assoc, incl_incl])
  map_id S := by apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]
  map_comp f g := by apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]

variable {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (v0 : C0 ⟶ D0) (hPB : IsPullback v0 c0 q (toR R))

abbrev cone : Cone (D R q) where
  pt := C0
  π := { app S := pullback.lift v0 (c0 ≫ toR S.unop.1) (by rw [hPB.w, Category.assoc, toR_incl])
         naturality S T h := by apply pullback.hom_ext <;> (dsimp only [D]; simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]) <;> simp }

lemma fstAff {S : Subalgebra k Ω} (h : R ≤ S) : IsAffineHom (pullback.fst q (incl h)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback q (incl h)).flip
    (by dsimp [incl]; infer_instance)

instance {S T : (J R)ᵒᵖ} (h : S ⟶ T) : IsAffineHom ((D R q).map h) := by
  have h1 := fstAff R q S.unop.2.1
  have h2 := fstAff R q T.unop.2.1
  have : IsAffineHom ((D R q).map h ≫ pullback.fst _ _) := by
    dsimp only [D]; rw [pullback.lift_fst]; exact h1
  have hs : IsSeparated (pullback.fst q (incl T.unop.2.1)) := @IsSeparated.of_isAffineHom _ _ _ h2
  exact IsAffineHom.of_comp _ (pullback.fst q (incl T.unop.2.1))

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {D0 : Scheme.{0}} (q : D0 ⟶ Sp R)
variable {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (v0 : C0 ⟶ D0) (hPB : IsPullback v0 c0 q (toR R))

abbrev specCone (s : Cone (D R q)) : Cone ((F R).op ⋙ Scheme.Spec) where
  pt := s.pt
  π := { app S := s.π.app S ≫ pullback.snd _ _
         naturality S T h := by
           have hw := s.w h
           rw [← hw]
           erw [Category.id_comp, Category.assoc, pullback.lift_snd]
           exact (Category.assoc _ _ _).symm }

def bL (hR : R.FG) (s : Cone (D R q)) : s.pt ⟶ Sp Ω := (specLim R hR).lift (specCone R q s)

lemma bL_fac (hR : R.FG) (s : Cone (D R q)) (j : (J R)ᵒᵖ) :
    bL R q hR s ≫ toR j.unop.1 = s.π.app j ≫ pullback.snd q (incl j.unop.2.1) :=
  (specLim R hR).fac (specCone R q s) j

lemma bL_uniq (hR : R.FG) (s : Cone (D R q)) (m : s.pt ⟶ Sp Ω)
    (hm : ∀ j : (J R)ᵒᵖ, m ≫ toR j.unop.1 = s.π.app j ≫ pullback.snd q (incl j.unop.2.1)) : m = bL R q hR s :=
  (specLim R hR).uniq (specCone R q s) m hm

def aL (hR : R.FG) (s : Cone (D R q)) : s.pt ⟶ D0 :=
  s.π.app (op (⟨R, le_rfl, hR⟩ : J R)) ≫ pullback.fst q (incl (le_refl R))

lemma aL_w (hR : R.FG) (s : Cone (D R q)) : aL R q hR s ≫ q = bL R q hR s ≫ toR R := by
  have := bL_fac R q hR s (op (⟨R, le_rfl, hR⟩ : J R))
  simp only [aL, Category.assoc, pullback.condition, incl_self, Category.comp_id]
  exact this.symm

def coneIsLimit (hR : R.FG) : IsLimit (cone R q c0 v0 hPB) where
  lift s := hPB.lift (aL R q hR s) (bL R q hR s) (aL_w R q hR s)
  fac s j := by
    have hw := s.w (homOfLE j.unop.2.1 : (⟨R, le_rfl, hR⟩ : J R) ⟶ j.unop).op
    apply pullback.hom_ext
    · simp only [cone, Category.assoc, pullback.lift_fst, IsPullback.lift_fst, aL, ← hw]
    · simp only [cone, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, IsPullback.lift_snd]
      exact bL_fac R q hR s j
  uniq s m hm := by
    apply hPB.hom_ext
    · rw [IsPullback.lift_fst, aL, ← hm]
      simp only [cone, Category.assoc, pullback.lift_fst]
    · rw [IsPullback.lift_snd]
      apply bL_uniq
      intro j
      rw [← hm j]
      simp only [cone, Category.assoc, pullback.lift_snd]

lemma lfp {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] : LocallyOfFinitePresentation p := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  haveI : IsNoetherianRing Γ(Sp k, U) := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance U V e)

end LateralTheory.E.LeafDescendMapPf
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace LateralTheory.E.LeafProjModelPf

theorem image_isReduced {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] : IsReduced f.image := by
  have hB := Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing
  have hred : ∀ U : Y.affineOpens, _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U) := fun U =>
    isReduced_of_injective _ (f.toImage_app_injective U)
  refine @isReduced_of_isReduced_stalk _ (fun z => ⟨?_⟩)
  rintro g ⟨n, e⟩
  obtain ⟨U, hzU, s, rfl⟩ := f.image.presheaf.exists_germ_eq g
  rw [← map_pow, ← map_zero (f.image.presheaf.germ _ z hzU).hom] at e
  obtain ⟨V, hzV, iU, iV, e'⟩ := f.image.presheaf.germ_eq z hzU hzU _ 0 e
  rw [map_pow, map_zero] at e'
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp hB hzV
  have h0 : f.image.presheaf.map (homOfLE hWV).op (f.image.presheaf.map iU.op s) = 0 := by
    have hx := congrArg (f.image.presheaf.map (homOfLE hWV).op) e'
    rw [map_pow, map_zero] at hx
    exact (hred ⟨W, hW⟩).eq_zero _ ⟨n, hx⟩
  rw [← f.image.presheaf.germ_res iU z hzV, ← f.image.presheaf.germ_res (homOfLE hWV) z hzW]
  simp only [CommRingCat.comp_apply] at h0 ⊢
  rw [h0, map_zero]

theorem image_irreducible {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IrreducibleSpace X] :
    IrreducibleSpace f.image := by
  have h1 : IsIrreducible (Set.range f.toImage) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
  have h2 := h1.closure
  rw [f.toImage.denseRange.closure_range] at h2
  exact (irreducibleSpace_def _).mpr h2

theorem leafImageIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] (hX : IsIntegral X) :
    IsIntegral f.image := by
  have := image_isReduced f
  have := image_irreducible f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def LeafQProjImm : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (N : ℕ) (φ : Spec (CommRingCat.of A) ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace k N),
    IsImmersion φ ∧ QuasiCompact φ ∧
    φ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N = Spec.map (CommRingCat.ofHom (algebraMap k A))

theorem LeafProjModel_of (h1 : LeafQProjImm) : LateralTheory.E.LeafCloseBCut.LeafProjModel := by
  intro k _ A _ _ _ _
  obtain ⟨N, φ, hi, hq, hc⟩ := h1 k A
  refine ⟨φ.image, φ.imageι ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N, φ.toImage, leafImageIntegral φ inferInstance,
    ?_, inferInstance, ?_⟩
  · have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
    infer_instance
  · rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact hc

end LateralTheory.E.LeafProjModelPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocPf

def overIso {R : Type} [CommRing R] (X : Scheme.{0}) (F G : Shv R)
    (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U))
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) :
    F.over X ≅ G.over X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun Y => (e Y.unop.left Y.unop.hom).toModuleIso) (by
    intro Y Y' f
    ext s
    have h := he f.unop.left Y.unop.hom s
    rw [Over.w f.unop] at h
    exact h))

def LocOver : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

theorem LeafLoc_of (hO : LocOver) : LateralTheory.E.LeafTwistPf.LeafLoc := by
  intro hy R _ X F G e he n
  exact hO hy R X F G ⟨overIso X F G e he⟩ n

abbrev secCx {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) : CochainComplex (ModuleCat.{1} (ULift.{1} R)) ℤ :=
  ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)).mapHomologicalComplex _).obj (res R F)

def LocSec : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ (secCx F X).homology n)

def LocSlice : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty ((secCx F X).homology n ≃+ (secCx G X).homology n)

theorem LocOver_of (hS : LocSec) (hL : LocSlice) : LocOver := by
  intro hy R _ X F G hi n
  obtain ⟨a⟩ := hS hy R X F n
  obtain ⟨b⟩ := hS hy R X G n
  obtain ⟨c⟩ := hL hy R X F G hi n
  exact ⟨(a.trans c).trans b.symm⟩

theorem LeafLoc_of' (hS : LocSec) (hL : LocSlice) : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LeafLoc_of (LocOver_of hS hL)

end LateralTheory.E.LeafLocPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafExtendCut

def LeafStalkValuation : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω) (x y : C)
  (hx : IsGenericPoint x (⊤ : Set C)), IsCurve c → y ≠ x →
    ValuationRing (C.presheaf.stalk y) ∧
      (letI := (C.presheaf.stalkSpecializes (hx.specializes (Set.mem_univ y))).hom.toAlgebra
       IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x))

def LeafLocalExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsProper p] (x y : C),
  IsGenericPoint x (⊤ : Set C) → ∀ (h : x ⤳ y), ValuationRing (C.presheaf.stalk y) →
    (letI := (C.presheaf.stalkSpecializes h).hom.toAlgebra
     IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x)) →
    ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X, ψ ≫ p = C.fromSpecStalk x ≫ sC →
      ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC

def LeafGlueExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsSeparated p] (x : C),
  IsGenericPoint x (⊤ : Set C) → ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X,
    (∀ y : C, ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC) →
      ∃ e : C ⟶ X, C.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = sC

theorem goal_of (h1 : LeafStalkValuation) (h2 : LeafLocalExtend) (h3 : LeafGlueExtend) :
    LateralTheory.E.LeafCurveVCut.LeafExtend := by
  intro k Ω _ _ _ X C0 p _ c0 x hc hx ψ hψ
  have : IsIntegral C0 := hc.1
  refine h3 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x hx ψ ?_
  intro y
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨U, hxU, f, hf1, hf2⟩ := spread_out_of_isGermInjective'
      (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p ψ hψ
    exact ⟨U, hxU, hxU, f, hf1.symm, hf2⟩
  · obtain ⟨hv, hfr⟩ := h1 Ω c0 x y hx hc hyx
    exact h2 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x y hx _ hv hfr ψ hψ

end LateralTheory.E.LeafExtendCut
end
end

section

namespace LateralTheory.E.LeafTrdegDimPf

open Algebra

theorem trdeg_le_card (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F) :
    Algebra.trdeg k F ≤ (s.card : Cardinal) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F :=
    ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.1 (h.isAlgebraic x)⟩
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := k) (A := F) (s : Set F)
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk (s : Set F) := Cardinal.mk_le_mk_of_subset hts
    _ = (s.card : Cardinal) := by simp

theorem LeafTrdegDim_of : LateralTheory.E.LeafCurveVCut.LeafTrdegDim := by
  intro k F Ω _ _ _ _ _ _ _ _ n s hs hF R hR
  have hFT : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨d, hd1, hd2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k R
  have h1 : Algebra.trdeg k R ≤ Algebra.trdeg k Ω :=
    trdeg_le_of_injective R.val Subtype.val_injective
  have h2 : Algebra.trdeg k Ω = Algebra.trdeg k F := GlobalTheory.trdeg_eq_of_isAlgebraic_top k F Ω
  have h3 := trdeg_le_card k F s hF
  have hdn : (d : Cardinal) ≤ (n : Cardinal) := by
    rw [← hd2]
    exact h1.trans (h2 ▸ h3.trans (by exact_mod_cast hs))
  have : d ≤ n := by exact_mod_cast hdn
  rw [hd1]
  exact_mod_cast this

end LateralTheory.E.LeafTrdegDimPf
end

section

namespace LateralTheory.E.E4

def LeafNoetherDim : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] B),
  Function.Injective g → g.Finite → s = 1

theorem LeafNoetherCurve_of (hD : LeafNoetherDim) : LeafNoetherCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨s, g, hg, hf⟩ := exists_finite_inj_algHom_of_fg k B
  obtain rfl := hD k B hB s g hg hf
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    (MvPolynomial.finSuccEquiv k 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))
  refine ⟨g.comp e.symm.toAlgHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem LeafUnitsFG_of_dim (hD : LeafNoetherDim) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_leaves (LeafNoetherCurve_of hD) hV

end LateralTheory.E.E4
end
