module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.KrullDimension
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] (j : G₀ ⟶ G)

abbrev RangeIsId : Prop := ∀ x : G.left, x ∈ Set.range j.left ↔
  x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

include j in
theorem unit_mem_fibre (s : S) : (η[G]).left s ∈ G.hom ⁻¹' {s} := by
  show G.hom ((η[G]).left s) = s
  rw [← Scheme.Hom.comp_apply, Over.w]
  rfl

theorem isConnected_fibre [IsOpenImmersion j.left] (hr : RangeIsId j) (s : S) :
    _root_.IsConnected (G₀.hom ⁻¹' {s}) := by
  have hw : ∀ x, G.hom (j.left x) = G₀.hom x := fun x => by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have himg : j.left '' (G₀.hom ⁻¹' {s}) = connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hr (j.left x)).1 ⟨x, rfl⟩
      rwa [hw, show G₀.hom x = s from hx] at this
    · intro hy
      have hys : G.hom y = s := connectedComponentIn_subset (G.hom ⁻¹' {s}) _ hy
      obtain ⟨x, rfl⟩ := (hr y).2 (by rwa [hys])
      exact ⟨x, by rw [Set.mem_preimage, ← hw, hys]; rfl, rfl⟩
  have hc : _root_.IsConnected (connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s)) :=
    isConnected_connectedComponentIn_iff.mpr (unit_mem_fibre j s)
  rw [← himg] at hc
  exact ⟨hc.nonempty.of_image, j.left.isOpenEmbedding.isInducing.isPreconnected_image.1 hc.isPreconnected⟩

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.PullbackFinitePoint


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔ (f.residueFieldMap x).hom.Finite := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  unfold Scheme.Hom.residueDegree RingHom.Finite
  constructor
  · intro h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  · intro h
    exact Module.finrank_pos.ne'

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private theorem residueFieldMap_surjective_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap, ConcreteCategory.comp_apply]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : f.residueDegree x ≠ 0 :=
  (_root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite f x).2
    (RingHom.Finite.of_surjective _ (residueFieldMap_surjective_of_surjectiveOnStalks f x))

end GlobalTheory.PullbackFinitePoint
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PPAS

variable {S S' : Scheme.{0}}

theorem one_comp_of_isGrpPullback {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) :
    (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h A'))
  let g : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have e2 : g ≫ (1 : A ⟶ A) = 1 := by simp
  have e3 := congrArg (fun z : Over.mk (A'.hom ≫ f) ⟶ A => z.left) e2
  simp only [Over.comp_left] at e3
  rw [← e3] at e
  exact e

end GlobalTheory.PPAS
end
end

section

set_option autoImplicit false

open TopologicalSpace

namespace GlobalTheory

theorem exists_finite_topologicalKrullDim_inter_add_one_le {T : Type} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] (Z : Set T) (hZ : IsClosed Z) :
    ∃ S : Set T, S.Finite ∧ ∀ C : Set T, IsClosed C → Disjoint S C →
      topologicalKrullDim (Z ∩ C : Set T) + 1 ≤ topologicalKrullDim Z := by
  obtain ⟨F, hF, hcl, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  choose g hg using fun t : F => QuasiSober.sober (hirr t.1 t.2) (hcl t.1 t.2)
  have := hF.to_subtype
  refine ⟨Set.range g, Set.finite_range g, fun C hC hd => ?_⟩
  refine topologicalKrullDim_add_one_le (hZ.inter hC) hZ ?_
  rintro x ⟨⟨t, ht, hxt⟩, -⟩
  exact ⟨g ⟨t, ht⟩, ⟨t, ht, (hg ⟨t, ht⟩).mem⟩, fun h => Set.disjoint_left.1 hd ⟨_, rfl⟩ h.2,
    (hg ⟨t, ht⟩).specializes hxt⟩

end GlobalTheory
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem derivation_iterate_leibniz {R : Type} [CommRing R] (D : Derivation ℤ R R) (a b : R) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : R) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>

    rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
    Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : (n.choose ij.2 : R) = (n.choose ij.1 : R) := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    ring

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqPull

theorem tensor_isPullback {S : Scheme.{0}} (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback _ _

theorem sq_of_grpPullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  intro S S₀ f B _ B₀ _ i h
  obtain ⟨hP, hM⟩ := h
  let T : Over S₀ := B₀ ⊗ B₀
  have hw : ∀ x : T ⟶ B₀, (x.left ≫ i) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
    intro x
    rw [Category.assoc, hP.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((fst B₀ B₀).left ≫ i) (hw _)
  let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((snd B₀ B₀).left ≫ i) (hw _)
  have h1 : (lift x₀ y₀).left ≫ (fst B B).left = (fst B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift x₀ y₀).left ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨(lift x₀ y₀).left, ?_, ?_, h1, h2⟩
  · have outer : IsPullback ((snd B₀ B₀).left ≫ i) (fst B₀ B₀).left B.hom (B₀.hom ≫ f) :=
      IsPullback.paste_horiz (tensor_isPullback B₀ B₀).flip hP
    have sq : IsPullback (lift x₀ y₀).left (fst B₀ B₀).left (fst B B).left i := by
      refine IsPullback.of_right (h₁₂ := (snd B B).left) (v₁₃ := B.hom) (h₂₂ := B.hom) ?_ h1
        (tensor_isPullback B B).flip
      rw [h2, hP.w]
      exact outer
    exact IsPullback.paste_vert sq hP
  · have := hM T (fst B₀ B₀) (snd B₀ B₀) x₀ y₀ rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at this
    exact this

end GlobalTheory.SqPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.EndLoc.HomFixGlue

variable {S H : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {AH BH : Over H} [GrpObj AH] [GrpObj BH]

def IsSol (π : H ⟶ S) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH) {T : Scheme.{0}} (t : T ⟶ S)
    (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (h : T ⟶ H) : Prop :=
  h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
    IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

def IsRestr {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    {A'' B'' : Over U} [GrpObj A''] [GrpObj B''] (Φ'' : A'' ⟶ B'') (ρA : A''.left ⟶ A'.left)
    (ρB : B''.left ⟶ B'.left) : Prop :=
  IsGrpPullback A'' A' g ρA ∧ IsGrpPullback B'' B' g ρB ∧ Φ''.left ≫ ρB = ρA ≫ Φ'.left

variable {π : H ⟶ S} {φA : AH.left ⟶ A.left} {φB : BH.left ⟶ B.left} {Φ : AH ⟶ BH}

theorem isRestr_pullback {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B') :
    IsRestr g Φ' ((Over.pullback g).map Φ') (pullback.fst A'.hom g) (pullback.fst B'.hom g) :=
  ⟨isGrpPullback_pullback A' g, isGrpPullback_pullback B' g, pullback.lift_fst _ _ _⟩

theorem IsSol.restr {T U : Scheme.{0}} {t : T ⟶ S} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {h : T ⟶ H}
    (hs : IsSol π φA φB Φ t A' B' φA' φB' Φ' h) {g : U ⟶ T} {A'' B'' : Over U} [GrpObj A''] [GrpObj B'']
    {Φ'' : A'' ⟶ B''} {ρA : A''.left ⟶ A'.left} {ρB : B''.left ⟶ B'.left} (hr : IsRestr g Φ' Φ'' ρA ρB) :
    IsSol π φA φB Φ (g ≫ t) A'' B'' (ρA ≫ φA') (ρB ≫ φB') Φ'' (g ≫ h) := by
  obtain ⟨h1, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs
  obtain ⟨rA, rB, rΦ⟩ := hr
  refine ⟨by rw [Category.assoc, h1], ρA ≫ ψA, ρB ≫ ψB, rA.comp pA, rB.comp pB, by rw [Category.assoc, eA],
    by rw [Category.assoc, eB], ?_⟩
  rw [← Category.assoc, rΦ, Category.assoc, eΦ, Category.assoc]

theorem IsRestr.factor {T U W : Scheme.{0}} {f : U ⟶ T} {k : W ⟶ U} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα] {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left}
    {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {AW BW : Over W} [GrpObj AW] [GrpObj BW]
    {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left} (hW : IsRestr (k ≫ f) Φ' ΦW ρAW ρBW) :
    ∃ (σA : AW.left ⟶ Aα.left) (σB : BW.left ⟶ Bα.left), IsRestr k Φα ΦW σA σB ∧ σA ≫ ρAα = ρAW ∧
      σB ≫ ρBα = ρBW := by
  obtain ⟨aα, bα, cα⟩ := hα
  obtain ⟨aW, bW, cW⟩ := hW
  have wA : ρAW ≫ A'.hom = (AW.hom ≫ k) ≫ f := by rw [aW.1.w, Category.assoc]
  have wB : ρBW ≫ B'.hom = (BW.hom ≫ k) ≫ f := by rw [bW.1.w, Category.assoc]
  refine ⟨aα.1.lift _ _ wA, bα.1.lift _ _ wB, ⟨aα.cancel (aW.congr rfl (aα.1.lift_fst _ _ wA).symm)
    (aα.1.lift_snd _ _ wA), bα.cancel (bW.congr rfl (bα.1.lift_fst _ _ wB).symm) (bα.1.lift_snd _ _ wB), ?_⟩,
    aα.1.lift_fst _ _ wA, bα.1.lift_fst _ _ wB⟩
  apply bα.1.hom_ext
  · rw [Category.assoc, Category.assoc, bα.1.lift_fst, cW, cα, ← Category.assoc, aα.1.lift_fst]
  · rw [Category.assoc, Category.assoc, bα.1.lift_snd, Over.w Φα, aα.1.lift_snd, ← Category.assoc, Over.w ΦW]

theorem IsSol.pull {T U W : Scheme.{0}} {t : T ⟶ S} {f : U ⟶ T} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα]
    {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left} {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {hα' : U ⟶ H}
    (hs : IsSol π φA φB Φ (f ≫ t) Aα Bα (ρAα ≫ φA') (ρBα ≫ φB') Φα hα') (k : W ⟶ U) {g : W ⟶ T} (hg : g = k ≫ f)
    {AW BW : Over W} [GrpObj AW] [GrpObj BW] {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left}
    (hW : IsRestr g Φ' ΦW ρAW ρBW) : IsSol π φA φB Φ (g ≫ t) AW BW (ρAW ≫ φA') (ρBW ≫ φB') ΦW (k ≫ hα') := by
  subst hg
  obtain ⟨σA, σB, hr, eA, eB⟩ := hα.factor hW
  have := hs.restr hr
  rw [← eA, ← eB]
  simp only [Category.assoc] at this ⊢
  exact this

theorem isSol_of_local (pbA : IsGrpPullback AH A π φA) (pbB : IsGrpPullback BH B π φB) {T : Scheme.{0}} {t : T ⟶ S}
    {A' B' : Over T} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'}
    (hA : IsGrpPullback A' A t φA') (hB : IsGrpPullback B' B t φB') {h : T ⟶ H} (hh : h ≫ π = t) {Idx : Type}
    {U : Idx → Scheme.{0}} (f : ∀ i, U i ⟶ T) (Aα Bα : ∀ i, Over (U i)) [∀ i, GrpObj (Aα i)] [∀ i, GrpObj (Bα i)]
    (Φα : ∀ i, Aα i ⟶ Bα i) (ρA : ∀ i, (Aα i).left ⟶ A'.left) (ρB : ∀ i, (Bα i).left ⟶ B'.left)
    (hr : ∀ i, IsRestr (f i) Φ' (Φα i) (ρA i) (ρB i))
    (hs : ∀ i, IsSol π φA φB Φ (f i ≫ t) (Aα i) (Bα i) (ρA i ≫ φA') (ρB i ≫ φB') (Φα i) (f i ≫ h))
    (hepi : ∀ (u v : A'.left ⟶ BH.left), (∀ i, ρA i ≫ u = ρA i ≫ v) → u = v) :
    IsSol π φA φB Φ t A' B' φA' φB' Φ' h := by
  have wA : φA' ≫ A.hom = (A'.hom ≫ h) ≫ π := by rw [hA.1.w, Category.assoc, hh]
  have wB : φB' ≫ B.hom = (B'.hom ≫ h) ≫ π := by rw [hB.1.w, Category.assoc, hh]
  refine ⟨hh, pbA.1.lift _ _ wA, pbB.1.lift _ _ wB,
    pbA.cancel (hA.congr hh.symm (pbA.1.lift_fst _ _ wA).symm) (pbA.1.lift_snd _ _ wA),
    pbB.cancel (hB.congr hh.symm (pbB.1.lift_fst _ _ wB).symm) (pbB.1.lift_snd _ _ wB),
    pbA.1.lift_fst _ _ wA, pbB.1.lift_fst _ _ wB, hepi _ _ fun i => ?_⟩
  obtain ⟨-, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs i
  obtain ⟨rA, rB, rΦ⟩ := hr i
  have hψA : ψA = ρA i ≫ pbA.1.lift _ _ wA := pbA.1.hom_ext (by rw [eA, Category.assoc, pbA.1.lift_fst])
    (by rw [pA.1.w, Category.assoc, pbA.1.lift_snd, ← Category.assoc (ρA i), rA.1.w, Category.assoc])
  have hψB : ψB = ρB i ≫ pbB.1.lift _ _ wB := pbB.1.hom_ext (by rw [eB, Category.assoc, pbB.1.lift_fst])
    (by rw [pB.1.w, Category.assoc, pbB.1.lift_snd, ← Category.assoc (ρB i), rB.1.w, Category.assoc])
  rw [← Category.assoc, ← rΦ, Category.assoc, ← hψB, eΦ, hψA, Category.assoc]

theorem lbIso_restr {XA XB A'l B'l A''l B''l : Scheme.{0}} {L : LB XA} {M : LB XB} (hL : L.IsLB) (hM : M.IsLB)
    {φA' : A'l ⟶ XA} {φB' : B'l ⟶ XB} {Φl : A'l ⟶ B'l} {ρA : A''l ⟶ A'l} {ρB : B''l ⟶ B'l} {Φ''l : A''l ⟶ B''l}
    (e : Φ''l ≫ ρB = ρA ≫ Φl) (iso : LBIso (L.pull φA') ((M.pull φB').pull Φl)) :
    LBIso (L.pull (ρA ≫ φA')) ((M.pull (ρB ≫ φB')).pull Φ''l) := by
  have hN := pull_isLB hM φB'
  have i1 : LBIso (L.pull (ρA ≫ φA')) ((M.pull φB').pull (Φ''l ≫ ρB)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp ρA rfl e iso
  have i2 : LBIso ((M.pull φB').pull (Φ''l ≫ ρB)) (((M.pull φB').pull ρB).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hN Φ''l rfl
  have i3 : LBIso (((M.pull φB').pull ρB).pull Φ''l) ((M.pull (ρB ≫ φB')).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hM ρB rfl)) Φ''l
  exact LBIso.trans (pull_isLB hL _) (pull_isLB hN _) (pull_isLB (pull_isLB hM _) _) i1
    (LBIso.trans (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) (pull_isLB (pull_isLB hM _) _) i2 i3)

theorem rep_of_affine : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro S A B _ _ L M hL hM H π AH _ BH _ φA φB Φ pbA pbB haff T t A' B' _ _ φA' φB' Φ' hA hB hΦ iso
  have key : ∀ (R : Type) [CommRing R] (f : Sp R ⟶ T), ∃! k : Sp R ⟶ H, IsSol π φA φB Φ (f ≫ t)
      ((Over.pullback f).obj A') ((Over.pullback f).obj B') (pullback.fst A'.hom f ≫ φA') (pullback.fst B'.hom f ≫ φB')
      ((Over.pullback f).map Φ') k := fun R _ f =>
    haff R (f ≫ t) ((Over.pullback f).obj A') ((Over.pullback f).obj B') _ _ ((Over.pullback f).map Φ')
      ((isRestr_pullback f Φ').1.comp hA) ((isRestr_pullback f Φ').2.1.comp hB) inferInstance
      (lbIso_restr hL hM (isRestr_pullback f Φ').2.2 iso)
  let 𝒜 := T.affineOpenCover
  let 𝒰 := 𝒜.openCover
  have hloc : ∀ i, ∃! k : 𝒰.X i ⟶ H, IsSol π φA φB Φ (𝒰.f i ≫ t) ((Over.pullback (𝒰.f i)).obj A')
      ((Over.pullback (𝒰.f i)).obj B') (pullback.fst A'.hom (𝒰.f i) ≫ φA') (pullback.fst B'.hom (𝒰.f i) ≫ φB')
      ((Over.pullback (𝒰.f i)).map Φ') k := fun i => key (𝒜.X i) (𝒰.f i)
  choose k hk hku using hloc
  have hagree : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ k i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ k j := by
    intro i j
    let 𝒲 := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover
    refine 𝒲.openCover.hom_ext _ _ fun l => ?_
    let g : Sp (𝒲.X l) ⟶ T := (𝒲.openCover.f l ≫ pullback.fst _ _) ≫ 𝒰.f i
    have hg : g = (𝒲.openCover.f l ≫ pullback.snd _ _) ≫ 𝒰.f j :=
      (Category.assoc _ _ _).trans ((congrArg (𝒲.openCover.f l ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have hu := key (𝒲.X l) g
    rw [← Category.assoc, ← Category.assoc]
    exact hu.unique (IsSol.pull (isRestr_pullback _ Φ') (hk i) _ rfl (isRestr_pullback g Φ'))
      (IsSol.pull (isRestr_pullback _ Φ') (hk j) _ hg (isRestr_pullback g Φ'))
  let hg := 𝒰.glueMorphisms k hagree
  have hι : ∀ i, 𝒰.f i ≫ hg = k i := 𝒰.ι_glueMorphisms k hagree
  have hh : hg ≫ π = t := 𝒰.hom_ext _ _ fun i => by rw [← Category.assoc, hι]; exact (hk i).1
  let pullbackGrp (G : Over T) [GrpObj G] (i : 𝒰.I₀) : GrpObj ((Over.pullback (𝒰.f i)).obj G) :=
    letI : (Over.pullback (𝒰.f i)).Monoidal := (Over.instBraidedPullback (f := (𝒰.f i))).toMonoidal
    Functor.grpObjObj (F := Over.pullback (𝒰.f i))
  letI : ∀ i, GrpObj ((Over.pullback (𝒰.f i)).obj A') := pullbackGrp A'
  letI : ∀ i, GrpObj ((Over.pullback (𝒰.f i)).obj B') := pullbackGrp B'
  have hsol : IsSol π φA φB Φ t A' B' φA' φB' Φ' hg :=
    isSol_of_local pbA pbB hA hB hh 𝒰.f (fun i => (Over.pullback (𝒰.f i)).obj A')
      (fun i => (Over.pullback (𝒰.f i)).obj B') (fun i => (Over.pullback (𝒰.f i)).map Φ')
      (fun i => pullback.fst A'.hom (𝒰.f i)) (fun i => pullback.fst B'.hom (𝒰.f i))
      (fun i => isRestr_pullback _ Φ') (fun i => by rw [hι]; exact hk i)
      (fun u v h => Scheme.Cover.hom_ext (Precoverage.ZeroHypercover.pullback₁ A'.hom 𝒰) u v h)
  refine ⟨hg, hsol, fun h' hs' => 𝒰.hom_ext _ _ fun i => ?_⟩
  rw [hι]
  exact hku i _ (IsSol.restr hs' (isRestr_pullback _ Φ'))

end GlobalTheory.EndLoc.HomFixGlue
end
end
