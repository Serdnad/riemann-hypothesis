module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3272
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibConn

theorem lfac {X P : Scheme.{0}} (j : X ⟶ P) [IsImmersion j] (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ P)
    (h : Set.range ν ⊆ Set.range j) : ∃ y₀ : Sp Ω ⟶ X, y₀ ≫ j = ν := by
  have h1 : Set.range ν ⊆ Set.range j.coborderRange.ι := by
    refine h.trans ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨j.liftCoborder x, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩
  let ν' := IsOpenImmersion.lift j.coborderRange.ι ν h1
  have hν' : ν' ≫ j.coborderRange.ι = ν := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range ν' ⊆ Set.range j.liftCoborder := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := h ⟨q, rfl⟩
    refine ⟨x, j.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hx, ← Scheme.Hom.comp_apply, hν']
  haveI : Surjective (pullback.snd j.liftCoborder ν') := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h2 ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd j.liftCoborder ν')
  have key : pullback.fst j.liftCoborder ν' ≫ j = pullback.snd j.liftCoborder ν' ≫ ν := by
    have := congrArg (· ≫ j.coborderRange.ι) (pullback.condition (f := j.liftCoborder) (g := ν'))
    simp only [Category.assoc, Scheme.Hom.liftCoborder_ι, hν'] at this
    exact this
  refine ⟨inv (pullback.snd j.liftCoborder ν') ≫ pullback.fst j.liftCoborder ν', ?_⟩
  rw [Category.assoc, key, IsIso.inv_hom_id_assoc]

theorem lsurj {X Y W Z : Scheme.{0}} (l : W ⟶ X) (f : X ⟶ Y) (ν : Z ⟶ Y)
    (h : ∀ z : (pullback f ν : Scheme.{0}), pullback.fst f ν z ∈ Set.range l)
    (hc : ConnectedSpace (pullback (l ≫ f) ν : Scheme.{0})) : ConnectedSpace (pullback f ν : Scheme.{0}) := by
  haveI : ConnectedSpace (pullback l (pullback.fst f ν) : Scheme.{0}) :=
    (pullbackRightPullbackFstIso f ν l).hom.homeomorph.connectedSpace_iff.2 hc
  refine Function.Surjective.connectedSpace (f := pullback.snd l (pullback.fst f ν)) ?_
    (pullback.snd l (pullback.fst f ν)).continuous
  intro z
  obtain ⟨w, hw⟩ := h z
  obtain ⟨d, -, hd⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
  exact ⟨d, hd⟩

theorem liso {W Y T P Z B : Scheme.{0}} (a : Y ⟶ B) (k : T ⟶ B) (e : W ⟶ pullback a k) [IsIso e]
    (j : Y ⟶ P) [Mono j] (y₀ : Z ⟶ Y) (hc : ConnectedSpace (pullback (y₀ ≫ a) k : Scheme.{0})) :
    ConnectedSpace (pullback (e ≫ pullback.fst a k ≫ j) (y₀ ≫ j) : Scheme.{0}) := by
  set F := e ≫ pullback.fst a k ≫ j with hF
  set G := y₀ ≫ j with hG
  have c0 : pullback.fst F G ≫ e ≫ pullback.fst a k = pullback.snd F G ≫ y₀ := by
    rw [← cancel_mono j]
    have := pullback.condition (f := F) (g := G)
    simp only [hF, hG, Category.assoc] at this ⊢
    exact this
  have c1 : (pullback.fst (y₀ ≫ a) k ≫ y₀) ≫ a = pullback.snd (y₀ ≫ a) k ≫ k := by
    rw [Category.assoc]; exact pullback.condition
  let m₀ : pullback (y₀ ≫ a) k ⟶ pullback a k := pullback.lift (pullback.fst _ _ ≫ y₀) (pullback.snd _ _) c1
  have c2 : (m₀ ≫ inv e) ≫ F = pullback.fst (y₀ ≫ a) k ≫ G := by
    simp only [hF, hG, m₀, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  let m : pullback (y₀ ≫ a) k ⟶ pullback F G := pullback.lift (m₀ ≫ inv e) (pullback.fst _ _) c2
  have c3 : pullback.snd F G ≫ y₀ ≫ a = (pullback.fst F G ≫ e ≫ pullback.snd a k) ≫ k := by
    rw [← Category.assoc, ← c0]
    simp only [Category.assoc, pullback.condition]
  let n : pullback F G ⟶ pullback (y₀ ≫ a) k := pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ e ≫ pullback.snd a k) c3
  let φ : pullback (y₀ ≫ a) k ≅ pullback F G :=
    { hom := m, inv := n
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [m, n, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
        · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
            Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [← cancel_mono e]
          apply pullback.hom_ext
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, IsIso.inv_hom_id_assoc,
              Category.id_comp]
            exact c0.symm
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
              Category.id_comp]
        · simp only [m, n, Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp] }
  haveI : IsIso φ.hom := Iso.isIso_hom φ
  exact φ.hom.homeomorph.connectedSpace_iff.1 hc

theorem lred {X Y Z W : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] (hs : Function.Surjective i)
    (s : Y ⟶ W) (h : Z ⟶ W) (hc : ConnectedSpace (pullback h s : Scheme.{0})) :
    ConnectedSpace (pullback h (i ≫ s) : Scheme.{0}) := by
  haveI : Surjective i := ⟨hs⟩
  let q := pullback.fst (pullback.snd h s) i
  have hq : Function.Surjective q := (inferInstance : Surjective q).surj
  haveI : Nonempty (pullback (pullback.snd h s) i : Scheme.{0}) :=
    ⟨(hq (Nonempty.some inferInstance)).choose⟩
  haveI : ConnectedSpace (pullback (pullback.snd h s) i : Scheme.{0}) := by
    refine connectedSpace_iff_univ.2 ⟨Set.univ_nonempty, ?_⟩
    refine (q.isClosedEmbedding.isInducing.isPreconnected_image).1 ?_
    rw [Set.image_univ, hq.range_eq]
    exact isPreconnected_univ
  exact (pullbackLeftPullbackSndIso h s i).hom.homeomorph.connectedSpace_iff.1 this

theorem fib_conn : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G'), (∀ (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback π (spMap (κ.comp (residue R))) : Scheme.{0})) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ PSpace R E.N), (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ConnectedSpace (pullback E.f ν : Scheme.{0}) := by
  intro R _ _ _ S π hπ G' _ hG E hconn Ω _ _ ν hex
  obtain ⟨g, hg, p, hp⟩ := hex
  obtain ⟨y, hy⟩ := (GlobalTheory.Mum.Emb.range_closed R S π G' E).1 g hg
  haveI := E.imm
  have hrange : Set.range ν ⊆ Set.range E.j := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p, hp, hy]
    exact ⟨y, rfl⟩
  obtain ⟨y₀, hy₀⟩ := lfac E.j Ω ν hrange
  let κ₀ : ResidueField R →+* Ω := (Spec.preimage (y₀ ≫ E.Y.hom)).hom
  have hκ₀ : y₀ ≫ E.Y.hom = spMap κ₀ := by
    simp [κ₀, spMap]
  haveI := hπ
  let ρ := spMap (residue R)
  let S₀ := pullback π ρ
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π ρ)
  let T := S₀.nilradical.subscheme
  let i : T ⟶ S₀ := S₀.nilradical.subschemeι
  haveI : IsReduced T := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian i
  have hi : Function.Surjective i := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    rfl
  let t := i ≫ pullback.fst π ρ
  let kk := i ≫ pullback.snd π ρ
  obtain ⟨e, l, -, hl1, hl2⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t kk inferInstance inferInstance
    (by show i ≫ pullback.fst π ρ ≫ π = (i ≫ pullback.snd π ρ) ≫ ρ; rw [pullback.condition, Category.assoc])
  apply lsurj l E.f ν
  · intro z
    have h1 : E.f (pullback.fst E.f ν z) = ν (pullback.snd E.f ν z) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 : ν (pullback.snd E.f ν z) = E.f g := by rw [Subsingleton.elim (pullback.snd E.f ν z) p, hp]
    have h4 : ∀ b : E.H.toScheme, PSpace.str R E.N (E.f b) = π (G'.hom (E.H.ι b)) := fun b => by
      rw [← Scheme.Hom.comp_apply, E.f_over]
      rfl
    have h2 : π (G'.hom (E.H.ι (pullback.fst E.f ν z))) = closedPoint R := by
      rw [← h4, h1, h3, h4, hg]
    have h5 : G'.hom (E.H.ι (pullback.fst E.f ν z)) ∈ Set.range (pullback.fst π ρ) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨closedPoint (ResidueField R), (IsLocalRing.comap_closedPoint (residue R)).trans h2.symm⟩
    obtain ⟨w, hw⟩ := h5
    obtain ⟨u, rfl⟩ := hi w
    obtain ⟨d, hd1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := t)
      (E.H.ι (pullback.fst E.f ν z)) u hw.symm
    refine ⟨d, E.H.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hl1, hd1]
  · rw [hl2, ← hy₀]
    apply liso E.Y.hom kk e.hom E.j y₀
    rw [hκ₀]
    apply lred i hi
    have hc := hconn Ω κ₀
    have hcomp : spMap (κ₀.comp (residue R)) = spMap κ₀ ≫ ρ := by
      simp only [ρ, spMap, ← Spec.map_comp]
      rfl
    rw [hcomp] at hc
    exact ((pullbackLeftPullbackSndIso π ρ (spMap κ₀)).symm ≪≫ pullbackSymmetry _ _).hom.homeomorph.connectedSpace_iff.1 hc

end GlobalTheory.Mum.FibConn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_common_scale_thetaConstants_at_trait : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (m N : ℕ) (e : Fin N → Ω), Odd m → 3 ≤ m → IsUnit (m : o) → N = m ^ (4 * S.g) → SymE ρ m e → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (emb : Ω →+* FractionRing V), (∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V))) → ∃ (K : Type) (_ : Field K) (io : FractionRing V →+* K) (N' : ℕ) (c : Fin N → K) (c' : Fin N' → K) (a : K), a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) ∧ (∀ j, io (emb (e j)) = symTup c j) ∧ (∀ x, ∃ b, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.SiegTh.TraitScale.exists_scale | exact GlobalTheory.SiegTh.TraitScale.exists_scale | (intros; apply GlobalTheory.SiegTh.TraitScale.exists_scale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.siegelThetaConstants_projectively_integral_anyBase : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → GlobalTheory.Poinc.ThetaInt F W f := by
  first | exact @GlobalTheory.SiegTh.ThIntAll.thetaInt_all | exact GlobalTheory.SiegTh.ThIntAll.thetaInt_all | (intros; apply GlobalTheory.SiegTh.ThIntAll.thetaInt_all <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibClosed

theorem closed_in_preimage {F X P B : Scheme.{0}} (p : F ⟶ B) (q : B ⟶ P) (φ : F ⟶ X) (g : X ⟶ P) [IsProper p]
    [IsPreimmersion q] [IsSeparated g] (h : φ ≫ g = p ≫ q) :
    ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' Set.range q = Set.range φ := by
  let m : F ⟶ pullback g q := pullback.lift φ p h
  have hm : m ≫ pullback.snd g q = p := pullback.lift_snd _ _ _
  have : IsProper (m ≫ pullback.snd g q) := by rw [hm]; infer_instance
  have : IsProper m := IsProper.of_comp m (pullback.snd g q)
  have hcl : IsClosed (Set.range m) := m.isClosedMap.isClosed_range
  have hemb : Topology.IsEmbedding (pullback.fst g q) := (pullback.fst g q).isEmbedding
  obtain ⟨C, hC, hCe⟩ := hemb.isInducing.isClosed_iff.1 hcl
  refine ⟨C, hC, ?_⟩
  rw [← Scheme.Pullback.range_fst, ← Set.image_preimage_eq_inter_range, hCe, ← Set.range_comp]
  congr 1
  ext x
  show (m ≫ pullback.fst g q) x = φ x
  rw [pullback.lift_fst]

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

theorem exists_redFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    [IsProper π] : ∃ (T : Scheme.{0}) (t : T ⟶ S) (k : T ⟶ Sp (ResidueField R)), IsLocallyNoetherian T ∧ IsReduced T ∧
      IsProper k ∧ t ≫ π = k ≫ spMap (residue R) ∧ Set.range t = π ⁻¹' {closedPoint R} := by
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  let Z : TopologicalSpace.Closeds S := ⟨π ⁻¹' {closedPoint R}, hcp.preimage π.continuous⟩
  let Z₀ : TopologicalSpace.Closeds (Sp R) := ⟨{closedPoint R}, hcp⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let t := I.subschemeι
  have hrt : Set.range t = π ⁻¹' {closedPoint R} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  have hr : Set.range (t ≫ π) ⊆ (Z₀ : Set (Sp R)) := by
    rintro _ ⟨x, rfl⟩
    have : t x ∈ Set.range t := ⟨x, rfl⟩
    rw [hrt] at this
    exact this
  have h1 : Scheme.IdealSheafData.vanishingIdeal Z₀ ≤ (t ≫ π).ker :=
    GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker (t ≫ π) Z₀ hr
  have h2 : (spMap (residue R)).ker ≤ Scheme.IdealSheafData.vanishingIdeal Z₀ := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    have hx' : x = closedPoint R := hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]
    refine subset_closure ⟨closedPoint (ResidueField R), ?_⟩
    rw [hx']
    exact IsLocalRing.comap_closedPoint (residue R)
  let k := IsClosedImmersion.lift (spMap (residue R)) (t ≫ π) (h2.trans h1)
  have hk : k ≫ spMap (residue R) = t ≫ π := IsClosedImmersion.lift_fac _ _ _
  have : IsProper (k ≫ spMap (residue R)) := by rw [hk]; infer_instance
  have : IsProper k := IsProper.of_comp k (spMap (residue R))
  exact ⟨I.subscheme, t, k, inferInstance, inferInstance, inferInstance, hk.symm, hrt⟩

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

theorem ap {A B : Scheme.{0}} {f f' : A ⟶ B} (h : f = f') (x : A) : f x = f' x := h ▸ rfl

theorem range_inter_fibre_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (H' : E.H.toScheme.Opens) (X : Scheme.{0}) (o : H'.toScheme ⟶ X) (g : X ⟶ PSpace R E.N), IsSeparated g → o ≫ g = H'.ι ≫ E.f → (∀ z : E.H.toScheme, π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ H') → ∀ w : PSpace R E.N, PSpace.str R E.N w = closedPoint R → ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' {w} = Set.range o ∩ g ⁻¹' {w} := by
  intro R _ _ _ S π hπ G' _ hG E H' X o g hg hog hH' w hw
  haveI := hπ
  haveI := hg
  obtain ⟨T, t, k, hTn, hTr, hk, htk, hrt⟩ := exists_redFibre R S π
  obtain ⟨e, l, -, hl, hlf⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t k hTn hTr htk
  have hover : ∀ p, π (G'.hom (E.H.ι (l p))) = closedPoint R := by
    intro p
    have h1 : E.H.ι (l p) = pullback.fst G'.hom t p := by
      rw [← ap hl p, Scheme.Hom.comp_apply]
    have h2 : G'.hom (pullback.fst G'.hom t p) = t (pullback.snd G'.hom t p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have h3 : t (pullback.snd G'.hom t p) ∈ Set.range t := ⟨_, rfl⟩
    rw [hrt] at h3
    rw [h1, h2]; exact h3
  have hrl : Set.range l ⊆ Set.range H'.ι := by
    rintro _ ⟨p, rfl⟩; rw [Scheme.Opens.range_ι]; exact hH' _ (hover p)
  let l' := IsOpenImmersion.lift H'.ι l hrl
  have hl' : l' ≫ H'.ι = l := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ z : H'.toScheme, g (o z) = w →
      ∃ p, l' p = z ∧ E.j (pullback.fst E.Y.hom k (e.hom p)) = w := by
    intro z hz
    have hfz : E.f (H'.ι z) = w := by
      rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hog]
    have hcl : π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R := by
      have := ap E.f_over (H'.ι z)
      simp only [Scheme.Hom.comp_apply] at this
      rw [← this, hfz, hw]
    obtain ⟨p, hp⟩ : E.H.ι (H'.ι z) ∈ Set.range (pullback.fst G'.hom t) := by
      rw [Scheme.Pullback.range_fst]
      show G'.hom _ ∈ Set.range t
      rw [hrt]; exact hcl
    have hlp : l p = H'.ι z := E.H.ι.isOpenEmbedding.injective (by
      rw [← hp, ← ap hl p, Scheme.Hom.comp_apply])
    refine ⟨p, H'.ι.isOpenEmbedding.injective (by rw [← hlp, ← ap hl' p, Scheme.Hom.comp_apply]), ?_⟩
    rw [← hfz, ← hlp]
    have h := ap hlf p
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  by_cases hy : ∃ y, E.j y = w
  · obtain ⟨y, rfl⟩ := hy
    haveI := E.imm
    let F := pullback (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y)
    let φ : F ⟶ X := pullback.fst _ _ ≫ e.inv ≫ l' ≫ o
    have hφ : φ ≫ g = pullback.snd _ _ ≫ (E.Y.left.fromSpecResidueField y ≫ E.j) := by
      simp only [φ, Category.assoc, hog]
      rw [reassoc_of% hl', hlf, Iso.inv_hom_id_assoc, pullback.condition_assoc]
    obtain ⟨C, hC, hCe⟩ := closed_in_preimage (pullback.snd (pullback.fst E.Y.hom k)
      (E.Y.left.fromSpecResidueField y)) _ φ g hφ
    have hrange : Set.range (E.Y.left.fromSpecResidueField y ≫ E.j) = {E.j y} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩
        have : E.Y.left.fromSpecResidueField y a ∈ Set.range (E.Y.left.fromSpecResidueField y) := ⟨a, rfl⟩
        rw [Scheme.range_fromSpecResidueField] at this
        rw [this]
      · rintro rfl
        have : y ∈ Set.range (E.Y.left.fromSpecResidueField y) := by
          rw [Scheme.range_fromSpecResidueField]; rfl
        obtain ⟨a, ha⟩ := this
        exact ⟨a, by rw [ha]⟩
    refine ⟨C, hC, ?_⟩
    rw [← hrange, hCe]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨(pullback.fst _ _ ≫ e.inv ≫ l') a, ?_⟩, ?_⟩
      · show o _ = φ a
        simp only [φ, Scheme.Hom.comp_apply]
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hφ]
        exact ⟨pullback.snd (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y) a,
          (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      rw [hrange] at hz
      obtain ⟨p, hp, hpj⟩ := key z hz
      have hyp : pullback.fst E.Y.hom k (e.hom p) = y := E.j.isEmbedding.injective hpj
      obtain ⟨a, ha⟩ : e.hom p ∈ Set.range (pullback.fst (pullback.fst E.Y.hom k)
          (E.Y.left.fromSpecResidueField y)) := by
        rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
        exact hyp
      refine ⟨a, ?_⟩
      simp only [φ, Scheme.Hom.comp_apply]
      have h := ap e.hom_inv_id p
      simp only [Scheme.Hom.comp_apply] at h
      rw [ha, h]
      exact congrArg o hp
  · refine ⟨∅, isClosed_empty, ?_⟩
    ext x
    simp only [Set.empty_inter, Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage,
      Set.mem_singleton_iff, false_iff, not_and]
    rintro ⟨z, rfl⟩ hz
    obtain ⟨p, -, hpj⟩ := key z hz
    exact hy ⟨_, hpj⟩

end GlobalTheory.Mum.FibClosed
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.siegelThetaConstants_projectively_integral : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (h : M.Z ⟶ PSpace (cycAway n) N), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ h = spMap S.R.val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  first | exact @GlobalTheory.SiegTh.ThInt.thetaInt | exact GlobalTheory.SiegTh.ThInt.thetaInt | (intros; apply GlobalTheory.SiegTh.ThInt.thetaInt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem fibre_theta_consts_in_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (J : Type) (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∀ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
    ∃ v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀, t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) := by
  intro W _ gQ J l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q _ ρ _ D e _ C u mo hmo hT K _ _ ev k₀ hk₀ hrat bT t ψ hψ hL
  haveI : IsAlgClosed k₀ := hk₀
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 hlo.pow t K (𝟙 _)
  obtain ⟨th, κ, hth, hκ, hy⟩ := GlobalTheory.T.exists_generator_thetaConstants_fibre V₁ D K ev k₀ (8 * gQ) (l ^ j) J bT _ t ψ hψ hL v₀ hv₀
  obtain ⟨M, lam, hM, hA⟩ := GlobalTheory.T.normalisedThetaConstant_eq_scalar_root_mul_unit l hl hlo j hj V₁ hCN hlu D _ C e u mo hmo hT K ev D.rig D.rig_gen th hth
  obtain ⟨c', hc'⟩ := (hmo 0).2
  have hev : ev (u 0 c') ≠ 0 := (hc'.map ev).ne_zero
  have key : ∀ a, ∃ w : K, w ∈ k₀ ∧ κ * v₀ a = lam * ev (u 0 c') * w := by
    intro a
    obtain ⟨y, hya⟩ := hy a
    obtain ⟨c₀, ζ, hζ, hc⟩ := hA y _ hya
    obtain ⟨r, hr, hr'⟩ := hrat 0 c₀ c' hc'
    have hζk : ζ ∈ k₀ := Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
    exact ⟨ζ * r, k₀.mul_mem hζk hr, by rw [hc, hr']; ring⟩
  choose w hw hkw using key
  by_cases hlam : lam = 0
  · refine ⟨fun _ => 0, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ 1 isUnit_one (fun a => ?_) hv₀
    have := hkw a
    rw [hlam, zero_mul, zero_mul] at this
    simp [(mul_eq_zero.1 this).resolve_left hκ]
  · refine ⟨fun a => ⟨w a, hw a⟩, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ ((lam * ev (u 0 c'))⁻¹ * κ)
      (IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero (mul_ne_zero hlam hev)) hκ)) (fun a => ?_) hv₀
    show w a = _
    rw [_root_.mul_assoc, hkw a, ← _root_.mul_assoc, inv_mul_cancel₀ (mul_ne_zero hlam hev), _root_.one_mul]

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.USep.thetaConst_eq_lam_root_mul | exact GlobalTheory.USep.thetaConst_eq_lam_root_mul | (intros; apply GlobalTheory.USep.thetaConst_eq_lam_root_mul <;> assumption)
end
