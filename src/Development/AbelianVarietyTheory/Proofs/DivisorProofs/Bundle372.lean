module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle300
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_filteredColimit_finiteType_int_rings : ∀ A : CommRingCat.{0}, ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj A), Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) := by
  first | (exact @GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (exact GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (intros; apply GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FinExt

def finTypeZ : ObjectProperty CommRingCat.{0} := fun A => Algebra.FiniteType ℤ A

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  (E : finTypeZ.ι.LeftExtension G)

lemma comp_eq_of_fac {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
    {c : Cocone D} (hc : IsColimit c) (s : Cocone (D ⋙ E.right))
    (X : finTypeZ.FullSubcategory) {j j' : J} (ψ : finTypeZ.ι.obj X ⟶ D.obj j)
    (ψ' : finTypeZ.ι.obj X ⟶ D.obj j') (h : ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j') :
    E.hom.app X ≫ E.right.map ψ ≫ s.ι.app j = E.hom.app X ≫ E.right.map ψ' ≫ s.ι.app j' := by
  obtain ⟨k, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j j'
  have hk : (ψ ≫ D.map a) ≫ c.ι.app k = (ψ' ≫ D.map b) ≫ c.ι.app k := by
    simpa only [Category.assoc, Cocone.w] using h
  obtain ⟨l, f, hf⟩ := (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj X) X.property J D c hc).2 k _ _ hk
  have e1 : s.ι.app j = E.right.map (D.map (a ≫ f)) ≫ s.ι.app l := (s.w (a ≫ f)).symm
  have e2 : s.ι.app j' = E.right.map (D.map (b ≫ f)) ≫ s.ι.app l := (s.w (b ≫ f)).symm
  rw [e1, e2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 3
  simpa only [Functor.map_comp, Category.assoc] using hf

end

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  {E : finTypeZ.ι.LeftExtension G}

theorem preservesFilteredColimits_of_isPointwiseLeftKanExtension
    (hE : E.IsPointwiseLeftKanExtension) : PreservesFilteredColimitsOfSize.{0, 0} E.right := by
  refine ⟨fun J _ _ => ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  have hfac := fun (g : CostructuredArrow finTypeZ.ι c.pt) =>
    (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj g.left) g.left.property J D c hc).1 g.hom
  choose j ψ hψ using hfac
  let t : ∀ s : Cocone (D ⋙ E.right), Cocone (CostructuredArrow.proj finTypeZ.ι c.pt ⋙ G) :=
    fun s =>
    { pt := s.pt
      ι := { app := fun g => E.hom.app g.left ≫ E.right.map (ψ g) ≫ s.ι.app (j g)
             naturality := by
               intro g g' f
               have hn := E.hom.naturality f.left
               dsimp at hn ⊢
               simp only [Category.comp_id]
               change G.map f.left ≫ _ = _
               erw [reassoc_of% hn, ← Functor.map_comp_assoc]
               exact comp_eq_of_fac E hc s g.left _ _
                 (by rw [Category.assoc, hψ g', hψ g]; exact CostructuredArrow.w f) } }
  have ht : ∀ (s : Cocone (D ⋙ E.right)) (X : finTypeZ.FullSubcategory) (φ : finTypeZ.ι.obj X ⟶ c.pt),
      E.hom.app X ≫ E.right.map φ ≫ (hE c.pt).desc (t s) =
        E.hom.app X ≫ E.right.map (ψ (CostructuredArrow.mk φ)) ≫ s.ι.app (j (CostructuredArrow.mk φ)) := by
    intro s X φ
    have := (hE c.pt).fac (t s) (CostructuredArrow.mk φ)
    exact (Category.assoc _ _ _).symm.trans this
  exact
  { desc := fun s => (hE c.pt).desc (t s)
    fac := fun s k => by
      apply (hE (D.obj k)).hom_ext'
      intro X φ
      have h1 := ht s X (φ ≫ c.ι.app k)
      simp only [Functor.mapCocone_ι_app]
      erw [← Functor.map_comp_assoc, h1]
      exact comp_eq_of_fac E hc s X _ _ (hψ _)
    uniq := fun s m hm => by
      apply (hE c.pt).hom_ext'
      intro X φ
      rw [ht s X φ]
      have h2 := hψ (CostructuredArrow.mk φ)
      dsimp at h2
      conv_lhs => rw [← h2, Functor.map_comp, Category.assoc]
      have h3 := hm (j (CostructuredArrow.mk φ))
      simp only [Functor.mapCocone_ι_app] at h3
      rw [h3] }

end

theorem exists_preservesFilteredColimits_isIso :
    ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜),
      ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧
        (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) := by
  intro 𝒜 _ _ M
  haveI : HasColimitsOfSize.{0, 1} 𝒜 := hasColimitsOfSizeShrink.{0, 1, 1, 1} 𝒜
  haveI : finTypeZ.ι.HasPointwiseLeftKanExtension (finTypeZ.ι ⋙ M) := fun _ => inferInstance
  let E := Functor.LeftExtension.mk _ (finTypeZ.ι.pointwiseLeftKanExtensionUnit (finTypeZ.ι ⋙ M))
  have hE : E.IsPointwiseLeftKanExtension :=
    finTypeZ.ι.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _
  let φ := hE.homFrom (Functor.LeftExtension.mk M (𝟙 _))
  refine ⟨E.right, φ.right, preservesFilteredColimits_of_isPointwiseLeftKanExtension hE,
    fun A hA => ?_⟩
  let X : finTypeZ.FullSubcategory := ⟨A, hA⟩
  have h1 : IsIso (E.hom.app X) := (hE (finTypeZ.ι.obj X)).isIso_hom_app
  have h2 : E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X) = 𝟙 _ := by
    have := congr_app (StructuredArrow.w φ) X
    simpa using this
  have h4 : IsIso (E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X)) := by
    rw [h2]; exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  exact IsIso.of_isIso_comp_left (E.hom.app X) (φ.right.app (finTypeZ.ι.obj X))

end GlobalTheory.FinExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothDimTangent

theorem smoothOfRelativeDimension_of_universal_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  intro B _ X s d hs H
  have loc : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧ SmoothOfRelativeDimension d (W.ι ≫ s) := by
    intro p
    obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth s p
    let _ := (s.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := h
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    have hP : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp B, U) Γ(X, V) := ⟨_, _, _, ‹_›, P, rfl⟩
    let k := AlgebraicClosure (X.residueField p)
    let x : Sp k ⟶ X := spMap (algebraMap (X.residueField p) k) ≫ X.fromSpecResidueField p
    have hr : Set.range x.base ⊆ (V : Set X) := by
      rintro _ ⟨y, rfl⟩
      have : x.base y ∈ Set.range (X.fromSpecResidueField p).base := ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
      rw [Scheme.range_fromSpecResidueField] at this
      rw [Set.mem_singleton_iff.1 this]
      exact hx
    obtain ⟨φ, ψ, h1, h2, h3⟩ := GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections B X s U V hU hV e d k x hr (H k x)
    have : Nontrivial Γ(X, V) := φ.domain_nontrivial
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth P.dimension
    have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Sp B, U)] := Algebra.IsStandardSmooth.free_kaehlerDifferential
    have hrank : Module.finrank Γ(X, V) (Ω[Γ(X, V)⁄Γ(Sp B, U)]) = P.dimension :=
      Module.finrank_eq_of_rank_eq hP.rank_kaehlerDifferential
    have hd : d = P.dimension := GlobalTheory.T.eq_of_universal_tangent_dualNumber _ _ k P.dimension d hrank φ ψ h1 h2 h3
    have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (s.appLE U V e).hom := hP
    have : IsAffine U := hU
    have : IsAffine V := hV
    have : SmoothOfRelativeDimension P.dimension (s.resLE U V e) :=
      (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
          ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso s U V e)).2 h'))
    have : SmoothOfRelativeDimension (P.dimension + 0) (V.ι ≫ s) := by
      rw [← Scheme.Hom.resLE_comp_ι s e]; infer_instance
    refine ⟨V, hx, ?_⟩
    rw [hd]; exact this
  choose W hW hd using loc
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd

end GlobalTheory.SmoothDimTangent
end

section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.tower_complex_lift_and_extension_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  first | exact @GlobalTheory.TowerLift.tower_lemmas | exact GlobalTheory.TowerLift.tower_lemmas | (intros; apply GlobalTheory.TowerLift.tower_lemmas <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact : ∀ (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C) (f : K ⟶ (SimplicialObject.const C).obj B), QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧ (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0, (ShortComplex.mk _ _ w).Exact) ∧ ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  first | (exact @GlobalTheory.EtC.AugExact.augmented_exact_iff) | (exact GlobalTheory.EtC.AugExact.augmented_exact_iff) | (intros; apply GlobalTheory.EtC.AugExact.augmented_exact_iff  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N], (∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (exact GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (intros; apply GlobalTheory.HomCount.nonempty_equiv_of_card_hom  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.lattice_dual_fourier_expansion_schwartz : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ),
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  first | exact @GlobalTheory.periodisation_hasSum_fourier_bilinForm | exact GlobalTheory.periodisation_hasSum_fourier_bilinForm | (intros; apply GlobalTheory.periodisation_hasSum_fourier_bilinForm <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_poly_pow_mul_eq_one' : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B → ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  first | (exact @GlobalTheory.exists_poly_pow_mul_eq_one) | (exact GlobalTheory.exists_poly_pow_mul_eq_one) | (intros; apply GlobalTheory.exists_poly_pow_mul_eq_one  <;> assumption)
end

section

set_option autoImplicit false
noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.TrBasisQuot

theorem isTranscendenceBasis_quot_polynomial {k : Type} [Field k] {m : ℕ}
    (p : Polynomial (MvPolynomial (Fin m) k)) (hp : Prime p) (hdeg : 0 < p.natDegree) :
    IsTranscendenceBasis k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
  classical
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let φ : MvPolynomial (Fin m) k →ₐ[k] Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p} :=
    (Ideal.Quotient.mkₐ k (Ideal.span {p})).comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k) _)
  have hφ : ∀ b, φ b = Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C b) := fun b => rfl
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
    by_contra hb0
    have := Polynomial.natDegree_le_of_dvd hb (Polynomial.C_ne_zero.2 hb0)
    rw [Polynomial.natDegree_C] at this
    omega
  have haev : MvPolynomial.aeval (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) = φ :=
    MvPolynomial.algHom_ext fun j => by simp [hφ]
  have hind : AlgebraicIndependent k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    rw [algebraicIndependent_iff_injective_aeval, haev]
    exact hinj
  rw [hind.isTranscendenceBasis_iff_isAlgebraic]
  have hS : ∀ b, φ b ∈ Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    intro b
    rw [Algebra.adjoin_range_eq_range_aeval, haev]
    exact AlgHom.mem_range_self φ b
  let ψ := RingHom.codRestrict φ.toRingHom (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j)))) (fun b => hS b)
  have hψ : Function.Injective ψ := fun a b h => hinj (congrArg Subtype.val h)
  have hr : IsAlgebraic (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      (Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X) := by
    refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff hψ).2 hp.ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hc : (algebraMap _ (Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p})).comp ψ =
        (Ideal.Quotient.mk (Ideal.span {p})).comp Polynomial.C := RingHom.ext fun b => rfl
    rw [hc, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self p
  have htop : Algebra.adjoin (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      {Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X} = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine Polynomial.induction_on q (fun b => ?_) (fun f g hf hg => ?_) (fun n b ih => ?_)
    · exact Subalgebra.algebraMap_mem _ (⟨φ b, hS b⟩ : Algebra.adjoin k _)
    · rw [map_add (f := _)]
      exact add_mem hf hg
    · rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem ih (Algebra.subset_adjoin rfl)
  have h1 := (Algebra.isAlgebraic_adjoin_singleton_iff).2 hr
  exact ⟨fun z => h1 z (by rw [htop]; trivial)⟩

theorem trBasis_mod_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F),
    AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) →
    ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A,
      IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  intro k F _ _ _ d u hu A hA t ht
  subst hA
  classical
  have ht0 : Irreducible (hu.aevalEquiv.symm t) :=
    (MulEquiv.irreducible_iff hu.aevalEquiv.symm.toMulEquiv).2 ht
  cases d with
  | zero =>
    exfalso
    have h := MvPolynomial.eq_C_of_isEmpty (hu.aevalEquiv.symm t)
    apply ht0.not_isUnit
    rw [h]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
    rw [h, hc, map_zero]
  | succ m =>
    obtain ⟨i, hi⟩ : ∃ i, (hu.aevalEquiv.symm t).degreeOf i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : (hu.aevalEquiv.symm t).totalDegree = 0 := by
        rw [MvPolynomial.totalDegree_eq_zero_iff]
        intro mm hmm x
        have := MvPolynomial.monomial_le_degreeOf x hmm
        rw [hcon x] at this
        omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
      apply ht0.not_isUnit
      rw [h0]
      refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
      rw [h0, hc, map_zero]
    let E := hu.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin (m + 1)) i)).trans
      (MvPolynomial.finSuccEquiv k m))
    have hdeg : 0 < (E t).natDegree := by
      have h1 : (E t).natDegree = ((MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) i))
          (hu.aevalEquiv.symm t)).degreeOf 0 :=
        MvPolynomial.natDegree_finSuccEquiv _
      have h2 := MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (0 : Fin (m + 1)) i).injective
        (p := hu.aevalEquiv.symm t) i
      rw [Equiv.swap_apply_right] at h2
      rw [h1, h2]
      omega
    have hpE : Prime (E t) :=
      ((MulEquiv.irreducible_iff E.toMulEquiv).2 ht).prime
    have hpt : Prime t := (MulEquiv.prime_iff E.toMulEquiv).1 hpE
    refine ⟨hpt, m, rfl, fun j => E.symm (Polynomial.C (MvPolynomial.X j)), ?_⟩
    have hI : Ideal.span {E t} = (Ideal.span {t}).map (E : _ →+* _) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    have hb := (Ideal.quotientEquivAlg (Ideal.span {t}) (Ideal.span {E t}) E hI).symm.isTranscendenceBasis
      (GlobalTheory.TrBasisQuot.isTranscendenceBasis_quot_polynomial (E t) hpE hdeg)
    have hfun : (⇑((Ideal.span {t}).quotientEquivAlg (Ideal.span {E t}) E hI).symm ∘ fun j : Fin m =>
        (Ideal.Quotient.mk (Ideal.span {E t})) (Polynomial.C (MvPolynomial.X j))) =
        fun j => Ideal.Quotient.mk (Ideal.span {t}) (E.symm (Polynomial.C (MvPolynomial.X j))) := by
      funext j
      simp only [Function.comp_apply, Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    rw [hfun] at hb
    exact hb

end GlobalTheory.TrBasisQuot
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent : ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) → Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → ∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom) := by
  first | exact @GlobalTheory.NilThicken.isNilpotent_ker_app | exact GlobalTheory.NilThicken.isNilpotent_ker_app | (intros; apply GlobalTheory.NilThicken.isNilpotent_ker_app <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_idealSheafData_of_isClopen_family : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W → ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  first | exact @GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | exact GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | (intros; apply GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

theorem _root_.GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  first | (exact @GlobalTheory.IdealGlue.exists_comap_eq) | (exact GlobalTheory.IdealGlue.exists_comap_eq) | (intros; apply GlobalTheory.IdealGlue.exists_comap_eq <;> assumption)
end
