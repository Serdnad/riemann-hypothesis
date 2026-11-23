module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelGroupLawDefinedAtTranslate
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothFlatAlgebraFiniteCoverDecomp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VectorFieldOrderAddOfProdStrictHenselian
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Mathlib.Tactic.Monotonicity.Lemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private theorem isFinite_pullback_unit_of_surjective_on_points (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ) (hG : _root_.GlobalTheory.SS.SmConn G)
    (hG' : _root_.GlobalTheory.SS.SmConn G') (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (i : G ⟶ G') [IsMonHom i]
    (hpts : ∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) :
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  unfold _root_.GlobalTheory.SS.SmConn at hG hG'
  obtain ⟨-, hsm, hsep, hqc, hgc⟩ := hG
  obtain ⟨-, hsm', hsep', hqc', hgc'⟩ := hG'
  have hw : i.left ≫ G'.hom = G.hom := Over.w i
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  have : ConnectedSpace G'.left := GeometricallyConnected.connectedSpace_of_subsingleton G'.hom
  have : IsIntegral G.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G.hom
  have : IsIntegral G'.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G'.hom
  have : LocallyOfFiniteType (i.left ≫ G'.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType i.left := locallyOfFiniteType_of_comp i.left G'.hom
  have : JacobsonSpace G'.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G'.hom
  have hcl : closedPoints G'.left ⊆ Set.range i.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hpts (Over.homMk (pointOfClosedPoint (K := k) G'.hom y hy)
      (pointOfClosedPoint_comp _ _ _))
    refine ⟨x.left (IsLocalRing.closedPoint k), ?_⟩
    have h := congrArg (fun φ : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G' => φ.left (IsLocalRing.closedPoint k)) hx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h.trans (pointOfClosedPoint_apply _ _ _ _)
  have hgen : i.left (genericPoint G.left) = genericPoint G'.left := by
    have hη : closure {genericPoint G.left} = Set.univ := genericPoint_spec G.left
    have h1 : closure (Set.range i.left) = Set.univ :=
      Set.eq_univ_of_univ_subset (closure_closedPoints (X := G'.left) ▸ closure_mono hcl)
    have h2 : Set.range i.left ⊆ closure {i.left (genericPoint G.left)} := by
      rintro _ ⟨x, rfl⟩
      exact map_mem_closure i.left.continuous (hη ▸ Set.mem_univ x) (by simp)
    have h3 : IsGenericPoint (i.left (genericPoint G.left)) Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← h1]
      simpa using closure_mono h2
    exact h3.eq (genericPoint_spec G'.left)
  have hq : i.left.QuasiFiniteAt (genericPoint G.left) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have hfib : ∀ a : i.left.fiber (i.left (genericPoint G.left)),
        i.left.fiberι _ a = genericPoint G.left := by
      intro a
      have ha : i.left.fiberι _ a ∈ i.left ⁻¹' {i.left (genericPoint G.left)} := by
        rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self a
      refine _root_.GlobalTheory.OntoFinite.eq_genericPoint (K := k) G'.hom i.left g (by rw [hw]; exact hgG)
        hgG' _ ?_
      rw [← hgen]; exact ha
    have : Subsingleton (i.left.fiber (i.left (genericPoint G.left))) :=
      ⟨fun a b => (i.left.fiberι _).isEmbedding.injective ((hfib a).trans (hfib b).symm)⟩
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun b => Subsingleton.elim b _
  have : LocallyQuasiFinite i.left :=
    _root_.GlobalTheory.OntoFinite.locallyQuasiFinite_of_quasiFiniteAt (K := k) i _ hq
  have hpb : IsPullback (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left
      (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left i.left (η[G'] : 𝟙_ _ ⟶ G').left :=
    IsPullback.map (Over.forget _) (IsPullback.of_hasPullback _ _)
  have : LocallyQuasiFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb ‹_›
  have hsec : (η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom) := by rw [hsec]; infer_instance
  have : IsClosedImmersion (η[G'] : 𝟙_ _ ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have : IsClosedImmersion (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb.flip ‹_›
  have hw2 : (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ 𝟙 _ =
      (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom := by
    exact (Over.w (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G'))).trans
      (Over.w (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G'))).symm
  have : QuasiCompact (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
    have h2 : QuasiCompact ((pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom) := inferInstance
    rw [← hw2, Category.comp_id] at h2
    exact h2
  have : IsLocallyArtinian (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of k)))
  exact IsFinite.of_locallyQuasiFinite _


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), _root_.GlobalTheory.SS.SmConn G →
    _root_.GlobalTheory.SS.SmConn G' → SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g G'.hom → ∀ i : G ⟶ G', IsMonHom i →
    (∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) →
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  intro k _ _ G G' _ _ g hG hG' hgG hgG' i _ hpts
  exact isFinite_pullback_unit_of_surjective_on_points k G G' g hG hG' hgG hgG' i hpts

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.indep_of_nested_special_fibre_images : ∀ C : Core, C.HasTests → (∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' → rPt p ≫ y = rPt p ≫ y' → ∃ (τ : C.Test y) (τ' : C.Test y'), ∀ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j → ∃ c' : Sp (kb p) ⟶ τ'.H.left, c' ≫ τ'.H.hom = rPt p ≫ spMap τ'.j ∧ c' ≫ τ'.f = c ≫ τ.f) → C.Indep := by
  first | exact @GlobalTheory.ZJ.Core.indep_of_special_fibres | exact GlobalTheory.ZJ.Core.indep_of_special_fibres | (intros; apply GlobalTheory.ZJ.Core.indep_of_special_fibres <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_lift_oneParameter_quotient_torus : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → ∃ j : Gm (Sp k) ⟶ G, IsMonHom j ∧ j ≫ q = f := by
  first | exact @GlobalTheory.SS.exists_lift_oneParameter | exact GlobalTheory.SS.exists_lift_oneParameter | (intros; apply GlobalTheory.SS.exists_lift_oneParameter <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.modelGroupLaw_definedAt_translate : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ z : (M.prod M).Y.left, ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧ DefAt (M.prod M) (M.twist (transl a)) (μ[A]) z := by
  first | exact @GlobalTheory.SS.defAt_mul_twist | exact GlobalTheory.SS.defAt_mul_twist | (intros; apply GlobalTheory.SS.defAt_mul_twist <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.smooth_flat_algebra_finite_cover_decomp : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → PerfectField (IsLocalRing.ResidueField R) → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra R (C i)) (φ : ∀ i, B →ₐ[R] C i), (∀ i, Algebra.Smooth R (C i) ∧ IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i)).toRingHom)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → ∃ (i : Fin n) (a' : C i →ₐ[R] R'), a'.comp (φ i) = a := by
  first | exact @GlobalTheory.SS.Smoothening.smoothening | exact GlobalTheory.SS.Smoothening.smoothening | (intros; apply GlobalTheory.SS.Smoothening.smoothening <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (A A' : Over (Sp K)) (I I' : Type) [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (D : I → VF A) (D' : I' → VF A'), IsFrame D → IsFrame D' → ∃ D₂ : I ⊕ I' → VF (A ⊗ A'), IsFrame D₂ ∧ ∀ (M : Model R A) (N : Model R A') (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D' π n → HasOrd (M.prod N) D₂ π (m + n) := by
  first | exact @GlobalTheory.SS.OrdProd.ord_prod | exact GlobalTheory.SS.OrdProd.ord_prod | (intros; apply GlobalTheory.SS.OrdProd.ord_prod <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.grpScheme_points_model_over_field : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  first | exact @GlobalTheory.SS.ModelPoints.points_model | exact GlobalTheory.SS.ModelPoints.points_model | (intros; apply GlobalTheory.SS.ModelPoints.points_model <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

theorem gen_of_cover {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} (V : A → Y.Opens) (J : A → K → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ LB.wchart L φ (J a))
    (h1 : ∀ a b y, y ∈ V a → y ∈ V b → trF φ ε (𝟙 Y) y (J a) (J b) = 1) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have glue : ∀ j : K → L.ι, ∃ s : Γ(Y, LB.wchart L φ j)ˣ, ∀ a y, y ∈ LB.wchart L φ j → y ∈ V a →
      gm (𝟙 Y) y _ s = trF φ ε (𝟙 Y) y j (J a) := by
    intro j
    have le : ∀ a, LB.wchart L φ j ⊓ V a ≤ LB.wchart L φ j ⊓ LB.wchart L φ (J a) :=
      fun a => inf_le_inf_left _ (hV a)
    have hu : ∀ a y, y ∈ LB.wchart L φ j ⊓ V a →
        gm (𝟙 Y) y _ (res (le a) ((LB.LinComb L φ ε).g j (J a))) = trF φ ε (𝟙 Y) y j (J a) := fun a y hy =>
      (gm_res (𝟙 Y) y (le a) hy _).trans (gm_linComb L φ ε (𝟙 Y) y j (J a) hy.1 (hV a hy.2))
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ j) (fun a => LB.wchart L φ j ⊓ V a) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨a, ha⟩ := hc y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy, ha⟩)
      (fun a => res (le a) ((LB.LinComb L φ ε).g j (J a))) (fun a b y hy => by
        refine (hu a y hy.1).trans (Eq.trans ?_ (hu b y hy.2).symm)
        rw [← trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hV a hy.1.2) (hV b hy.2.2), h1 a b y hy.1.2 hy.2.2, _root_.mul_one])
    refine ⟨s, fun a y h₁ h₂ => ?_⟩
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j ⊓ V a := ⟨h₁, h₂⟩
    exact (gm_res (𝟙 Y) y inf_le_left hm s).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs a)).trans (hu a y hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  refine ((gm_res (𝟙 Y) y _ hy _).trans (hs j a y hy.1 ha)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (hs j' a y hy.2 ha))).trans ?_)
  exact trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hV a ha)

def Fix {X : Scheme.{0}} (φ : X ⟶ X) (U : X.Opens) (f : Γ(X, U)) (n : ℕ) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n

theorem Fix.id {X : Scheme.{0}} (U : X.Opens) (f : Γ(X, U)) : Fix (𝟙 X) U f 1 := by
  refine ⟨rfl, ?_⟩
  simp [Scheme.Hom.appLE]
  exact rs_self (X := X) le_rfl f

theorem Fix.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {U : X.Opens} {f : Γ(X, U)} {a b : ℕ}
    (h : Fix φ U f a) (h' : Fix ψ U f b) : Fix (φ ≫ ψ) U f (a * b) := by
  obtain ⟨e, h⟩ := h
  obtain ⟨e', h'⟩ := h'
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e', ← e], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e'.le e.le, CommRingCat.hom_comp, RingHom.comp_apply, h', map_pow, h,
    pow_mul]

theorem Fix.pow {S : Scheme.{0}} {G : Over S} {F : End G} {U : G.left.Opens} {f : Γ(G.left, U)} {q m : ℕ}
    (h : Fix (F ^ m).asHom.left U f (q ^ m)) (l : ℕ) :
    Fix (F ^ (m * l)).asHom.left U f (q ^ (m * l)) := by
  induction l with
  | zero => exact Fix.id U f
  | succ l ih =>
    rw [mul_add, Nat.mul_one, pow_add, pow_add, mul_comm (q ^ _)]
    exact h.comp ih

theorem Fix.gm {X : Scheme.{0}} {φ : X ⟶ X} {U : X.Opens} {f : Γ(X, U)ˣ} {n : ℕ} (h : Fix φ U f.val n)
    (x : X) (hx : x ∈ U) : gm φ x U f = gm (𝟙 X) x U f ^ n := by
  obtain ⟨e, h⟩ := h
  have hx' : φ x ∈ U := e.le hx
  have h2 : res e.le (pullU φ U f) = f ^ n := Units.ext h
  rw [← map_pow, ← h2, gm_res (𝟙 X) x e.le hx, gm_pull (𝟙 X) φ x U hx', Category.id_comp]

theorem pullPow_of_fix {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : X ⟶ X) (n : ℕ)
    {A : Type} (V : A → X.Opens) (c : A → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ L.U (c a))
    (h : ∀ a b, Fix φ (V a ⊓ V b) (res (inf_le_inf (hV a) (hV b)) (L.g (c a) (c b))).val n) :
    PullPow φ L n := by
  refine gen_of_cover hL _ _ V (fun a _ => c a) hc (fun a y hy => Set.mem_iInter.2 fun k => ?_) fun a b y ha hb => ?_
  · fin_cases k
    · exact hV a ((h a a).1.le ⟨hy, hy⟩).1
    · exact hV a hy
  · have hm : y ∈ V a ⊓ V b := ⟨ha, hb⟩
    have e := (h a b).gm y hm
    have hm' : φ y ∈ V a ⊓ V b := (show V a ⊓ V b ≤ φ ⁻¹ᵁ (V a ⊓ V b) from (h a b).1.le) hm
    rw [gm_res φ y _ hm', gm_res (𝟙 X) y _ hm] at e
    simp only [trF, Fin.prod_univ_two, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one, e]
    simp

theorem frob_pullPow : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (F : End G) (q : ℕ), FrobG G F q → ∀ L : LB G.left, L.IsLB → ∃ m, 1 ≤ m ∧ ∀ l, PullPow (F ^ (m * l)).asHom.left L ((q : ℤ) ^ (m * l)) := by
  intro k _ G _ hG F q hF L hL
  classical
  obtain ⟨-, -, hsep, hqc, -⟩ := hG
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hx : ∀ x : G.left, ∃ (V : G.left.Opens) (i : L.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨_, ⟨V, hV, rfl⟩, h₁, h₂⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hi (L.U i).isOpen
    exact ⟨V, i, hV, h₁, h₂⟩
  choose V c hA hxV hV using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set G.left)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  choose m hm hfix using fun p : s × s => hF.2 (V p.1 ⊓ V p.2) ((hA p.1).inf (hA p.2))
    (res (inf_le_inf (hV p.1) (hV p.2)) (L.g (c p.1) (c p.2))).val
  refine ⟨∏ p, m p, Finset.one_le_prod' fun p _ => hm p, fun l => ?_⟩
  have := pullPow_of_fix hL (F ^ ((∏ p, m p) * l)).asHom.left (q ^ ((∏ p, m p) * l))
    (fun a : s => V a) (fun a => c a) (fun y => by
      obtain ⟨a, ha, hy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
      exact ⟨⟨a, ha⟩, hy⟩) (fun a => hV a) (fun a b => by
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (a, b))
      rw [hr, Nat.mul_assoc]
      exact Fix.pow (hfix (a, b)) _)
  exact_mod_cast this

end GlobalTheory.SS.FrobLB
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smooth_of_smooth_thickenings' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (B : Over (Spec (CommRingCat.of R))), IsProper B.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, Smooth (Y e).hom) → Smooth B.hom := by
  first | exact @GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings | exact GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings | (intros; apply GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings <;> assumption)
end
