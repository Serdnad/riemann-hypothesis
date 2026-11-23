module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlane
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle152
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle038
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht.FlagBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comp_listProd {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (e : X ⟶ Y) (L : List (Y ⟶ G)) :
    e ≫ L.prod = (L.map (e ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one e
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem isCombAtG_bc {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (a j)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  have he : spMap (dualMap ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom := by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap ψ)) he
  refine ⟨fun i => e ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMap ψ) ≫ v i
    rw [hu i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, epsMul, _root_.mul_comm]
  · have hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [hl, ← comp_listProd, Over.comp_left, hw]
    rfl

end GlobalTheory.LocM.Cht.FlagBase
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.MemberGlue

theorem exists_immersion_of_closed_pieces : ∀ (P : Scheme.{0}) (ι : Type) [Finite ι] (C : ι → Scheme.{0}) [∀ a, IsAffine (C a)] [∀ a, IsReduced (C a)] (h : ∀ a, C a ⟶ P) (W : ι → P.Opens) (h' : ∀ a, C a ⟶ (W a).toScheme), IsLocallyNoetherian P → (∀ a, h' a ≫ (W a).ι = h a) → (∀ a, IsClosedImmersion (h' a)) → (∀ a a', Set.range (h a') ∩ (W a : Set P) ⊆ Set.range (h a)) → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ a, C a ⟶ F), IsImmersion f ∧ (∀ a, IsOpenImmersion (i a)) ∧ (∀ a, i a ≫ f = h a) ∧ ∀ x : F, ∃ a, x ∈ Set.range (i a) := by
  intro P ι _ C _ _ h W h' _ hh hcl hag
  have hpt : ∀ a c, (W a).ι (h' a c) = h a c := fun a c => by rw [← hh a]; rfl
  let U : P.Opens := ⨆ a, W a
  let Φ : Set P := ⋃ a, Set.range (h a)
  let O : ι → Set P := fun a => (W a).ι '' (Set.range (h' a))ᶜ
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (W a).ι.isOpenEmbedding.isOpenMap _ (h' a).isClosedEmbedding.isClosed_range.isOpen_compl
  have hW : ∀ a c, h a c ∈ (W a : Set P) := fun a c => by
    rw [← hpt a c]; exact (h' a c).2
  have hU : ∀ a, (W a : Set P) ⊆ U := fun a =>
    SetLike.coe_subset_coe.mpr (le_iSup W a)
  have hΦ : U.ι ⁻¹' Φ = (U.ι ⁻¹' ⋃ a, O a)ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx hxO
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, w, hw, e⟩ := Set.mem_iUnion.mp hxO |>.imp fun _ h => h
      have h1 : U.ι x ∈ Set.range (h a') ∩ (W a : Set P) :=
        ⟨⟨c', hc'⟩, e ▸ w.2⟩
      obtain ⟨c, hc⟩ := hag a a' h1
      exact hw ⟨c, (W a).ι.isOpenEmbedding.injective ((hpt a c).trans (hc.trans e.symm))⟩
    · intro hx
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
      have h2 : (⟨x.1, ha⟩ : (W a).toScheme) ∈ Set.range (h' a) := by
        by_contra hn
        exact hx (Set.mem_iUnion.mpr ⟨a, ⟨x.1, ha⟩, hn, rfl⟩)
      obtain ⟨c, hc⟩ := h2
      exact Set.mem_iUnion.mpr ⟨a, c, by rw [← hpt a c, hc]; rfl⟩
  let Z : TopologicalSpace.Closeds U.toScheme := ⟨U.ι ⁻¹' Φ, by
    rw [hΦ]
    exact ((isOpen_iUnion hO).preimage U.ι.continuous).isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g : I.subscheme ⟶ U.toScheme := I.subschemeι
  let f : I.subscheme ⟶ P := g ≫ U.ι
  have hrg : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hfΦ : ∀ x, f x ∈ Φ := fun x => by
    have : g x ∈ (Z : Set U.toScheme) := hrg ▸ ⟨x, rfl⟩
    exact this
  have hfinj : Function.Injective f := f.isEmbedding.injective
  have hrU : ∀ a, Set.range (h a) ⊆ Set.range U.ι := fun a => by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU a (hW a c)
  let k : ∀ a, C a ⟶ U.toScheme := fun a => IsOpenImmersion.lift U.ι (h a) (hrU a)
  have hk : ∀ a, k a ≫ U.ι = h a := fun a => IsOpenImmersion.lift_fac _ _ _
  have hkZ : ∀ a, Set.range (k a) ⊆ Z := fun a => by
    rintro _ ⟨c, rfl⟩
    change U.ι (k a c) ∈ Φ
    have : U.ι (k a c) = h a c := by rw [← hk a]; rfl
    rw [this]
    exact Set.mem_iUnion.mpr ⟨a, c, rfl⟩
  have hker : ∀ a, g.ker ≤ (k a).ker := fun a => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker (k a) Z (hkZ a)
  let i : ∀ a, C a ⟶ I.subscheme := fun a => IsClosedImmersion.lift g (k a) (hker a)
  have hig : ∀ a, i a ≫ g = k a := fun a => IsClosedImmersion.lift_fac _ _ _
  have hif : ∀ a, i a ≫ f = h a := fun a => by
    rw [← hk a, ← hig a, Category.assoc]
  have hipt : ∀ a c, f (i a c) = h a c := fun a c => by rw [← hif a]; rfl
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  refine ⟨I.subscheme, f, i, inferInstance, fun a => ?_, hif, fun x => ?_⟩
  · let V : I.subscheme.Opens := f ⁻¹ᵁ W a
    have hiV : Set.range (i a) ⊆ Set.range V.ι := by
      rintro _ ⟨c, rfl⟩
      rw [Scheme.Opens.range_ι]
      change f (i a c) ∈ W a
      rw [hipt]
      exact hW a c
    have hrW : Set.range (V.ι ≫ f) ⊆ Set.range (W a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let j : C a ⟶ V.toScheme := IsOpenImmersion.lift V.ι (i a) hiV
    have hj : j ≫ V.ι = i a := IsOpenImmersion.lift_fac _ _ _
    let r : V.toScheme ⟶ (W a).toScheme := IsOpenImmersion.lift (W a).ι (V.ι ≫ f) hrW
    have hr : r ≫ (W a).ι = V.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have hjr : j ≫ r = h' a := by
      rw [← cancel_mono (W a).ι, Category.assoc, hr, reassoc_of% hj, hif, hh]
    have : Mono r := by
      have : Mono (r ≫ (W a).ι) := by rw [hr]; infer_instance
      exact mono_of_mono r (W a).ι
    have : IsClosedImmersion (j ≫ r) := by rw [hjr]; infer_instance
    have : IsClosedImmersion j := IsClosedImmersion.of_comp j r
    have : Surjective j := ⟨fun y => by
      have hy : f (V.ι y) ∈ (W a : Set P) := y.2
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp (hfΦ (V.ι y))
      obtain ⟨c, hc⟩ := hag a a' ⟨⟨c', hc'⟩, hy⟩
      refine ⟨c, V.ι.isOpenEmbedding.injective (hfinj ?_)⟩
      have : V.ι (j c) = i a c := by rw [← hj]; rfl
      rw [this, hipt, hc]⟩
    have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
    rw [← hj]
    infer_instance
  · obtain ⟨a, c, hc⟩ := Set.mem_iUnion.mp (hfΦ x)
    exact ⟨a, c, hfinj ((hipt a c).trans hc)⟩

end GlobalTheory.MemberGlue
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
namespace GlobalTheory

theorem preimage_opens_eq_range_of_valuative (F Z X : Scheme.{0}) (j : F ⟶ Z) (π : Z ⟶ X) (U : X.Opens)
    (hj : IsOpenImmersion j) (hd : Dense (Set.range j)) (hπ : IsSeparated π)
    (hF : TopologicalSpace.NoetherianSpace F) (hU : Set.range (j ≫ π) ⊆ (U : Set X))
    (hv : ∀ (A K : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
      [IsFractionRing A K] (a : Sp K ⟶ F) (b : Sp A ⟶ X), Set.range b ⊆ (U : Set X) →
      a ≫ j ≫ π = spMap (algebraMap A K) ≫ b →
      ∃ l : Sp A ⟶ F, spMap (algebraMap A K) ≫ l = a ∧ l ≫ j ≫ π = b) :
    π ⁻¹' (U : Set X) = Set.range j := by
  have hg : Set.range (j ≫ π).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hU
  let g : F ⟶ U := IsOpenImmersion.lift U.ι (j ≫ π) hg
  have hgfac : g ≫ U.ι = j ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hj' : Set.range j.base ⊆ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  let j' : F ⟶ (π ⁻¹ᵁ U : Z.Opens) := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hj'
  have hj'fac : j' ≫ (π ⁻¹ᵁ U).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomp : j' ≫ (π ∣_ U) = g := by
    rw [← cancel_mono U.ι, hgfac, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'fac]
  haveI : QuasiCompact g := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : UniversallyClosed g := by
    apply UniversallyClosed.of_valuativeCriterion
    intro S
    obtain ⟨l, hl1, hl2⟩ := hv S.R S.K S.i₁ (S.i₂ ≫ U.ι)
      (by
        rintro _ ⟨x, rfl⟩
        rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
      (by rw [← hgfac, ← Category.assoc, S.commSq.w, Category.assoc])
    have hl3 : l ≫ g = S.i₂ := by
      rw [← cancel_mono U.ι, Category.assoc, hgfac, hl2]
    exact ⟨⟨{ l := l, fac_left := hl1, fac_right := hl3 }⟩⟩
  haveI : UniversallyClosed (j' ≫ (π ∣_ U)) := by rw [hcomp]; infer_instance
  haveI : IsSeparated ((π ⁻¹ᵁ U).ι ≫ π) := inferInstance
  haveI : IsSeparated ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  haveI : IsSeparated (π ∣_ U) := IsSeparated.of_comp (π ∣_ U) U.ι
  haveI : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (π ∣_ U)
  have hclosed : IsClosed (Set.range j'.base) := j'.isClosedMap.isClosed_range
  have hrange : Set.range j' = (π ⁻¹ᵁ U).ι ⁻¹' Set.range j := by
    ext w; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (π ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hj'fac, hx]
  have hdense : Dense (Set.range j') := by
    rw [hrange]; exact hd.preimage (π ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap
  have huniv : Set.range j' = Set.univ := by
    rw [← hclosed.closure_eq]; exact hdense.closure_eq
  ext z; constructor
  · intro hz
    have hz' : z ∈ Set.range (π ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨x, rfl⟩ : w ∈ Set.range j' := huniv ▸ Set.mem_univ w
    exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, rfl⟩; exact hU ⟨x, rfl⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ProjFinProd

theorem exists_isProjOver_finite_prod : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  intro O _ ι _ X s
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro Y f hs hf
    rename_i α β
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (e i)) (fun i => f (e i)) hs (fun i => hf _)
    have key : ∀ j : β, ∃ q : P ⟶ Y j, q ≫ f j = p0 ≫ s ∧ ∀ i (h : e i = j), q = p i ≫ eqToHom (congrArg Y h) := by
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      refine ⟨p i, hp i, fun i' h => ?_⟩
      obtain rfl := e.injective h
      simp
    choose q hq1 hq2 using key
    have hq : ∀ i, q (e i) = p i := fun i => by simpa using hq2 (e i) i rfl
    refine ⟨P, p0, q, hP, hq1, fun Z a b hb => ?_⟩
    obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (e i)) (fun i => hb _)
    refine ⟨h, ⟨h1, fun j => ?_⟩, fun h' hh => h3 h' ⟨hh.1, fun i => ?_⟩⟩
    · obtain ⟨i, rfl⟩ := e.surjective j
      rw [hq]; exact h2 i
    · rw [← hq]; exact hh.2 _
  | h_empty =>
    intro Y f hs hf
    refine ⟨X, 𝟙 X, fun i => i.elim, by simpa using hs, fun i => i.elim, fun Z a b _ => ?_⟩
    exact ⟨a, ⟨by simp, fun i => i.elim⟩, fun h hh => by simpa using hh.1⟩
  | h_option ih =>
    intro Y f hs hf
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (some i)) (fun i => f (some i)) hs (fun i => hf _)
    refine ⟨pullback (p0 ≫ s) (f none), pullback.fst _ _ ≫ p0,
      fun i => match i with
        | none => pullback.snd _ _
        | some i => pullback.fst _ _ ≫ p i, ?_, ?_, fun Z a b hb => ?_⟩
    · rw [Category.assoc]
      exact isProjOver_pullback hP (hf none)
    · rintro (_ | i)
      · simp only [Category.assoc]; exact pullback.condition.symm
      · simp only [Category.assoc]; rw [hp i]
    · obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (some i)) (fun i => hb _)
      refine ⟨pullback.lift h (b none) (by rw [reassoc_of% h1, hb]), ⟨?_, ?_⟩, fun h' hh => ?_⟩
      · rw [pullback.lift_fst_assoc, h1]
      · rintro (_ | i)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h2 i)
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine h3 _ ⟨by simpa using hh.1, fun i => ?_⟩
          simpa using hh.2 (some i)
        · rw [pullback.lift_snd]; exact hh.2 none

end GlobalTheory.ProjFinProd
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsCharExt

section Ring

variable (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]

end Ring

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def pull {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a') :
    (Over.mk a ⟶ t.G) →* (Over.mk a' ⟶ t.G) where
  toFun w := (Over.homMk g h : Over.mk a' ⟶ Over.mk a) ≫ w
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

end GlobalTheory.TorsCharExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.majorant_harnack_holomorphic_half_plane : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (x : ℂ → Frame X.Ψ N), DifferentiableOn ℂ x {w | T < w.im} → (∀ w : ℂ, T < w.im → x w ∈ X.dom) → ∀ w w' : ℂ, T < w.im → T < w'.im → ∀ (τ : X.Ψ) (v : Fin N → ℂ), X.maj (x w') τ v ≤ (2 + ‖w - w'‖ ^ 2 / ((w.im - T) * (w'.im - T))) * X.maj (x w) τ v := by
  first | exact @GlobalTheory.maj_harnack | exact GlobalTheory.maj_harnack | (intros; apply GlobalTheory.maj_harnack <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (la : Wt X.Ψ N) (P : Frame X.Ψ N → ℂ) (ξ : Fin N → E), P ∈ X.SS la → X.IsIso ξ → ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt ξ x τ) → X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  first | exact @GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | exact GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | (intros; apply GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso <;> assumption)
end
