module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointEqOfReductionCoords
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioOfWeightSums
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_poly_normSq_roots' : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ (F : End B) (q : ℕ), IsMonHom F.asHom → PullPow F.asHom.left L q → ∃ P : Polynomial ℤ, P ≠ 0 ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q) ∧ ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), polyPt F P x = 1 := by
  exact @GlobalTheory.SS.exists_poly_normSq_roots
end

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
theorem _root_.GlobalTheory.SS.finite_ker_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G], _root_.GlobalTheory.SS.SmConn G → ∀ f : G ⟶ G, IsMonHom f →
    (∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ f = y) →
    Finite {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1} := by
  intro k _ _ G _ hG f _ hpts
  have hG0 := hG
  unfold _root_.GlobalTheory.SS.SmConn at hG0
  obtain ⟨-, hsm, -, -, hgc⟩ := hG0
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected G.hom ((η[G] : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k))
  have hK := isFinite_pullback_unit_of_surjective_on_points k G G g hG hG hg hg f hpts
  have hKhom : (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom = (pullback.snd f (η[G] : 𝟙_ _ ⟶ G)).left := by
    rw [← Over.w (pullback.snd f (η[G] : 𝟙_ _ ⟶ G))]; rfl
  have : IsFinite (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom := hKhom ▸ hK
  have hfin : Finite (pullback f (η[G] : 𝟙_ _ ⟶ G)).left := by
    have h := (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom.finite_preimage_singleton
      (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact Set.finite_univ_iff.mp
      (h.subset fun p _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))
  have hone : ∀ x : {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1},
      x.1 ≫ f = 𝟙 _ ≫ (η[G] : 𝟙_ _ ⟶ G) := fun x => by
    rw [x.2, Category.id_comp]; rfl
  refine Finite.of_injective (fun x => (pullback.lift x.1 (𝟙 _) (hone x)).left
    (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))) ?_
  intro x y hxy
  have : LocallyOfFiniteType (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  have : Subsingleton (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : IsReduced (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have hl : (pullback.lift x.1 (𝟙 _) (hone x)).left = (pullback.lift y.1 (𝟙 _) (hone y)).left := by
    have : LocallyOfFiniteType ((pullback.lift x.1 (𝟙 _) (hone x)).left ≫
        (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom) := by rw [Over.w]; infer_instance
    refine ext_of_apply_eq (K := k) (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom Set.univ
      isClosed_univ.isLocallyClosed dense_univ (fun p _ _ => ?_) ((Over.w _).trans (Over.w _).symm)
    obtain rfl := Subsingleton.elim p (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact hxy
  have hl' : pullback.lift x.1 (𝟙 _) (hone x) = pullback.lift y.1 (𝟙 _) (hone y) := Over.OverMorphism.ext hl
  apply Subtype.ext
  have := congrArg (· ≫ pullback.fst f (η[G] : 𝟙_ _ ⟶ G)) hl'
  rw [pullback.lift_fst, pullback.lift_fst] at this
  exact this

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.exists_oneParameterSubgroup_of_rational_family : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), SmConn G → IsChart G j ε f → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t * t') ≠ 0 → (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t * t')) ≫ j) → ∃ F : Gm (Sp k) ⟶ G, IsMonHom F ∧ F ≠ 1 := by
  first | exact @GlobalTheory.SS.ArcInf.exists_oneParameter_of_rational_family | exact GlobalTheory.SS.ArcInf.exists_oneParameter_of_rational_family | (intros; apply GlobalTheory.SS.ArcInf.exists_oneParameter_of_rational_family <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem natCast_self_residueField_padicAlgCl_eq_zero (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : kb p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO p)), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  have : (((p : ℕ) : OO p) : PadicAlgCl p) = (p : PadicAlgCl p) := rfl
  rw [this, PadicAlgCl.valuation_p]
  have h1 : (1 : NNReal) < p := by exact_mod_cast hp.out.one_lt
  rw [div_lt_one (lt_trans zero_lt_one h1)]
  exact h1

theorem ker_isMaximal_of_forall_pow_eq_one {A k : Type*} [CommRing A] [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) (φ : A →+* k) :
    (RingHom.ker φ).IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨by simp, fun J a hJ ha haJ => ?_⟩
  obtain ⟨n, hn, h⟩ := hk (φ a) ha
  have h1 : 1 - a ^ n ∈ J := hJ (by simp [RingHom.mem_ker, h])
  have h2 : a ^ n ∈ J := J.pow_mem_of_mem haJ n hn
  simpa using J.add_mem h1 h2

theorem isClosed_image_point_of_forall_pow_eq_one {k : Type} [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) {X : Scheme.{0}} [JacobsonSpace X]
    (x : Sp k ⟶ X) (s : Sp k) : IsClosed ({x s} : Set X) := by
  obtain ⟨V, hV, φ, rfl⟩ := exists_affineOpen_factor_of_isLocalRing x
  have h := hV.fromSpec.isOpenEmbedding.preimage_closedPoints
  have hs : Spec.map φ s ∈ closedPoints (Spec Γ(X, V)) := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr ?_
    have := (s : PrimeSpectrum k).isPrime
    have e : (s : PrimeSpectrum k).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have : (Spec.map φ s : PrimeSpectrum Γ(X, V)).asIdeal = RingHom.ker φ.hom := by
      change Ideal.comap φ.hom (s : PrimeSpectrum k).asIdeal = _
      rw [e]; rfl
    rw [this]
    exact ker_isMaximal_of_forall_pow_eq_one hk φ.hom
  rw [← h] at hs
  rw [Scheme.Hom.comp_apply]
  exact hs

theorem exists_residueField_factor_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}}
    (x : Sp k ⟶ X) (s : Sp k) (z : X) (hz : x s = z) :
    ∃ r : X.residueField z ⟶ CommRingCat.of k, Spec.map r ≫ X.fromSpecResidueField z = x := by
  obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst hz
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x⟩

theorem exists_integral_point_lifting_residue_point :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens),
      (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime],
        (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧
        (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  intro X _ π _ _ U hU p hp
  obtain ⟨hJ, hfin, -⟩ := jacobson_closedPoints_tools_int X π
  obtain ⟨-, hord, hgal⟩ := GlobalTheory.T.kb_isAlgClosed_and_conj' p
  have hcl : ∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X) :=
    fun x s => isClosed_image_point_of_forall_pow_eq_one hord x s
  refine ⟨fun x => ?_, hcl⟩
  let s : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hlift : ∃ (q : ℕ) (_ : Fact q.Prime) (y : Sp (OO q) ⟶ X),
      y (IsLocalRing.closedPoint (OO q)) = x s ∧ Set.range (gPt q ≫ y) ⊆ U := by
    obtain ⟨q, hq, hqz⟩ := exists_prime_residueField_eq_zero π (hcl x s)
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨K, hK, y, hy, hyU, -⟩ := exists_padic_point_scheme π (hcl x s) hqz U hU
    have hmem (a : PadicAlgCl q) : a ∈ OO q ↔ ‖a‖ ≤ 1 := by
      rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]
      rfl
    let j : integralClosure ℤ_[q] K →+* OO q :=
      (K.val.toRingHom.comp (integralClosure ℤ_[q] K).val.toRingHom).codRestrict (OO q)
        fun a => (hmem _).mpr ((mem_integralClosure_padicInt_iff K _).mp a.2)
    haveI : IsLocalHom j := by
      refine ⟨fun a ha => ?_⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : ((a : K) : PadicAlgCl q) * (b : PadicAlgCl q) = 1 :=
        congrArg (fun z : OO q => (z : PadicAlgCl q)) hb
      have ha0 : (a : K) ≠ 0 := by
        intro h
        rw [h] at hb'
        simp at hb'
      have hinv : (a : K)⁻¹ ∈ integralClosure ℤ_[q] K := by
        rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv,
          ← eq_inv_of_mul_eq_one_right hb']
        exact (hmem _).mp b.2
      exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
    letI : IsLocalRing (integralClosure ℤ_[q] K) := j.domain_isLocalRing
    refine ⟨q, inferInstance, spMap j ≫ y, ?_, ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
      exact IsLocalRing.comap_closedPoint j
    · rintro _ ⟨t, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      have key : spMap j ((gPt q) t) = genericPoint (Sp (integralClosure ℤ_[q] K)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        apply le_antisymm _ bot_le
        intro a ha
        have ha' : ((a : K) : PadicAlgCl q) ∈ (t : PrimeSpectrum (PadicAlgCl q)).asIdeal := ha
        haveI := (t : PrimeSpectrum (PadicAlgCl q)).isPrime
        rw [Ideal.eq_bot_of_prime (t : PrimeSpectrum (PadicAlgCl q)).asIdeal,
          Ideal.mem_bot] at ha'
        exact Subtype.ext (Subtype.ext ha')
      rw [Scheme.Hom.comp_apply, key]
      exact hyU
  obtain ⟨q, hq, y, hy, hyU⟩ := hlift
  have hfz := hfin _ (hcl x s)
  obtain ⟨r', hr'⟩ := exists_residueField_factor_of_apply_eq x s _ rfl
  have hy' : (rPt q ≫ y) (IsLocalRing.closedPoint (kb q)) = x s := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO q))
  obtain ⟨r, hr⟩ := exists_residueField_factor_of_apply_eq (rPt q ≫ y) _ _ hy'
  obtain rfl : p = q := by
    have h1 : ((p : ℕ) : X.residueField (x s)) = 0 := by
      apply r'.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero p
    have h2 : ((q : ℕ) : X.residueField (x s)) = 0 := by
      apply r.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero q
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hp.out).mpr h1
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hq.out).mpr h2
    exact CharP.eq (X.residueField (x s)) ‹CharP _ p› ‹CharP _ q›
  obtain ⟨σ, hσ⟩ := hgal (X.residueField (x s)) r.hom r'.hom
  refine ⟨spMap σ.toRingHom ≫ y, ?_, ?_⟩
  · let τ : kb p →+* kb p := IsLocalRing.ResidueField.map (σ : OO p →+* OO p)
    have e1 : rPt p ≫ spMap σ.toRingHom = spMap τ ≫ rPt p := by
      refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
      rfl
    have e2 : r ≫ CommRingCat.ofHom τ = r' := by
      ext a
      obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (r.hom a)
      change τ (r.hom a) = r'.hom a
      rw [← hσ a c hc, ← hc]
      rfl
    rw [← Category.assoc, e1, Category.assoc]
    refine (congrArg (spMap τ ≫ ·) hr.symm).trans (Eq.trans ?_ hr')
    rw [← e2, Spec.map_comp, Category.assoc]
  · rintro _ ⟨t, rfl⟩
    apply hyU
    refine ⟨t, ?_⟩
    simp only [Scheme.Hom.comp_apply]
    congr 1
    have := (t : PrimeSpectrum (PadicAlgCl p)).isPrime
    have e : (t : PrimeSpectrum (PadicAlgCl p)).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    apply PrimeSpectrum.ext
    ext a
    change (a : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal ↔
      ((σ a : OO p) : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal
    rw [e]
    simp

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.classical_point_eq_of_reduction_coords : ∀ C : Core, C.HasTests → C.Fib → ∀ (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), C.Coord w W hw u → ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme), C.Cl (a ≫ W.ι ≫ C.GG.hom) → a ≫ W.ι ≫ C.GG.hom = a' ≫ W.ι ≫ C.GG.hom → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' → (∀ i, a.appTop.hom (W.topIso.inv.hom (u i)) = a'.appTop.hom (W.topIso.inv.hom (u i))) → a = a' := by
  first | exact @GlobalTheory.ZJ.classical_eq_of_coord | exact GlobalTheory.ZJ.classical_eq_of_coord | (intros; apply GlobalTheory.ZJ.classical_eq_of_coord <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_ratio_of_weight_sums' : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∀ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → ∃ (U' : G.left.Opens) (h : U' ≤ U) (n : ℕ) (a b : Fin n → Γ(G.left, U')) (χ : Fin n → X), (U' : Set G.left).Nonempty ∧ (∀ j, Wt i U' (a j) (χ j) ∧ Wt i U' (b j) (χ j) ∧ (a j = 0 ∨ IsUnit (a j)) ∧ (b j = 0 ∨ IsUnit (b j))) ∧ IsUnit (∑ j, b j) ∧ (G.left.presheaf.map (homOfLE h).op).hom f * ∑ j, b j = ∑ j, a j := by
  first | exact @GlobalTheory.SS.WtRat.exists_ratio_of_weight_sums | exact GlobalTheory.SS.WtRat.exists_ratio_of_weight_sums | (intros; apply GlobalTheory.SS.WtRat.exists_ratio_of_weight_sums <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem Mod.integral_of_weight_zero_dominates : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (a : Sp (PadicAlgCl p) ⟶ G.left) (w : J → PadicAlgCl p), a ≫ G.hom = gPt p ≫ spMap j → Crd H σ a w → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a := by
  intro p _ V _ j G _ g N N' X _ q H J _ σ cls m hB a w ha hw hi
  obtain ⟨ν, hν, hc⟩ := m.ser a ha w hw
  apply hc
  let e : m.Φ.E.X ≃ₗ[ℤ] X := m.xe.toIntLinearEquiv
  have : Module.Free ℤ X := Module.Free.of_equiv e
  have : Module.Finite ℤ X := Module.Finite.equiv e
  have hq : ∀ x : X, (q.comp m.xe.toIntLinearEquiv.toLinearMap) (m.xe.symm x) = q x := by
    intro x
    rw [QuadraticMap.comp_apply]
    exact congrArg q (m.xe.apply_symm_apply x)
  refine GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max X q g N J cls p w ν ?_ ?_ hB.lll ?_ hν hi
  · have h := m.good.pos.comp (m.xe.symm.injective.tendsto_cofinite)
    exact h.congr hq
  · exact e.finrank_eq.symm.le.trans ((Nat.le_add_left _ _).trans m.dim.le)
  · intro i n
    have h := m.good.short i (m.xe.symm n)
    rw [← map_nsmul, ← map_add (f := _), hq, hq] at h
    exact h

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaModel_torsion_rational_over_fractionField : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N → ∀ y : Over.mk (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V) ⟶ u.G, y ^ m = 1 → ∃ x : Sp (FractionRing u.V) ⟶ u.G.left, spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ x = y.left := by
  first | exact @GlobalTheory.UnitTheta.torsion_rational | exact GlobalTheory.UnitTheta.torsion_rational | (intros; apply GlobalTheory.UnitTheta.torsion_rational <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformised_model_labelled_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  first | exact @GlobalTheory.ZH.utest_torsion_points | exact GlobalTheory.ZH.utest_torsion_points | (intros; apply GlobalTheory.ZH.utest_torsion_points <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weilPairing_labelledTorsion_uniformTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  first | exact @GlobalTheory.ZH.weilIs_uTest | exact GlobalTheory.ZH.weilIs_uTest | (intros; apply GlobalTheory.ZH.weilIs_uTest <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integral_torsion_point_descends_to_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  first | exact @GlobalTheory.ZH.torsion_integral_descends | exact GlobalTheory.ZH.torsion_integral_descends | (intros; apply GlobalTheory.ZH.torsion_integral_descends <;> assumption)
end
