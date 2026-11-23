module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle069
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.VertCoeffRing
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def tvE (u : TanM (𝟙 (Sp R)) G) : epsR R ⟶ G := Over.homMk (tv u).left (by
  have := Over.w (tv u)
  simpa using this)

theorem tvE_left (u : TanM (𝟙 (Sp R)) G) : (tvE u).left = (tv u).left := rfl

end GlobalTheory.VertCoeffRing
end
end

section

noncomputable section

namespace GlobalTheory.SiegPt

section Algebra

open Polynomial IsLocalRing

end Algebra

section Level

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp unitOn omegaStd IsGrpPullback LBIso pushPt)

theorem sec_bijective {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] (X : Over (Sp O)) [IsProper X.hom]
    (e : Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ 𝟙_ (Over (Sp O))) :
    Function.Bijective fun x : 𝟙_ (Over (Sp O)) ⟶ X => e ≫ x := by
  have he : e.left = Geo.Tor.spMap (algebraMap O C) := (Category.comp_id _).symm.trans (Over.w e)
  have hE : ValuativeCriterion.Existence X.hom := by
    have h : UniversallyClosed X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness X.hom := IsSeparated.valuativeCriterion X.hom
  let S : (Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ X) → ValuativeCommSq X.hom := fun z =>
    { R := O, K := C, i₁ := z.left, i₂ := 𝟙 _, commSq := ⟨(Over.w z).trans (Category.comp_id _).symm⟩ }
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h₁ : Geo.Tor.spMap (algebraMap O C) ≫ x.left = (e ≫ x).left := congrArg (· ≫ x.left) he.symm
    have h₂ : Geo.Tor.spMap (algebraMap O C) ≫ y.left = (e ≫ x).left :=
      (congrArg (· ≫ y.left) he.symm).trans (congrArg Over.Hom.left hxy.symm)
    have := (hU (S (e ≫ x))).elim ⟨x.left, h₁, Over.w x⟩ ⟨y.left, h₂, Over.w y⟩
    exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)
  · obtain ⟨⟨l, h1, h2⟩⟩ := hE (S z)
    refine ⟨Over.homMk l h2, Over.OverMorphism.ext ?_⟩
    show e.left ≫ l = z.left
    rw [he]
    exact h1

theorem exists_secHom {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] {Q : Out.PolAV (Sp O)}
    {Q' : Out.PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left}
    (H : IsGrpPullback Q'.A Q.A (Geo.Tor.spMap (algebraMap O C)) ψ) (hw' : LBIso Q'.L (Q.L.pull ψ)) :
    ∃ ρ : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (𝟙_ (Over (Sp C)) ⟶ Q'.A), Function.Bijective ρ ∧
      ∀ (n : ℕ) x y (u : Oˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map (algebraMap O C).toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have := Q.isAb.comm
  have := Q.isAb.proper
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let β := algebraMap O C
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv H
  let e : Over.mk (Geo.Tor.spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (Geo.Tor.spMap β) (Category.comp_id _)
  let r : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (Over.mk (Geo.Tor.spMap β) ⟶ Q.A) :=
    MonoidHom.mk' (fun x => e ≫ x) fun x y => MonObj.comp_mul _ _ _
  have hρ : ∀ x, (b.symm (r x)).left ≫ ψ = Geo.Tor.spMap β ≫ x.left := fun x => by
    rw [← hb, b.apply_symm_apply]; rfl
  refine ⟨b.symm.toMonoidHom.comp r, b.symm.bijective.comp (sec_bijective Q.A e), fun n x y u hx hy hw => ?_⟩
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hw' _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (hρ x) (hρ y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (IsFractionRing.injective O C h₅)
  exact hc

theorem exists_level {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (P : Out.PolAV (Sp O)) (h M : ℕ) (ze : Oˣ) (hg : P.g = h) (hM : IsUnit (M : O))
    (hz : IsPrimitiveRoot (algebraMap O C ze) M) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp O)) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
      (∀ x, lev x ^ M = 1) ∧ ∀ x y, Out.WeilIs P.A P.L M (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  subst hg
  have hM' : (M : C) ≠ 0 := by
    have := (hM.map (algebraMap O C)).ne_zero
    rwa [map_natCast] at this
  haveI : NeZero M := ⟨fun h0 => hM' (by rw [h0, Nat.cast_zero])⟩
  obtain ⟨P', g, hg, hgg, hmul, tw, htw⟩ :=
    GlobalTheory.laws_without_cohomology.2.2.1 _ _ (Geo.Tor.spMap (algebraMap O C)) P
  have hp : IsGrpPullback P'.A P.A (Geo.Tor.spMap (algebraMap O C)) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  obtain ⟨ρ, hρ, hw⟩ := exists_secHom hp (Geo.Tor.LBIso.symm ⟨tw, htw⟩)
  obtain ⟨lev⟩ := nonempty_level_of_isAlgClosed C P' M (Units.map (algebraMap O C).toMonoidHom ze) hM'
    (IsPrimitiveRoot.coe_units_iff.1 hz)
  rw [← hgg]
  have := P'.isAb.comm
  choose t ht using fun a : Fin P'.g ⊕ Fin P'.g → ℤ =>
    hρ.2 (LevelCompare.homOfBasis lev (Multiplicative.ofAdd (fun j => (a j : ZMod M))))
  have tors : ∀ a, t a ^ M = 1 := fun a => hρ.1 (by rw [map_pow, ht, map_one, LevelCompare.hom_pow])
  refine ⟨t, fun a b => hρ.1 ?_, tors, fun a b => hw M _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, ← map_mul, ← ofAdd_add]
    exact congrArg _ (congrArg _ (funext fun j => Int.cast_add _ _))
  · rw [ht, ht, map_zpow]
    have w := LevelCompare.pairing_of_basis lev a b
    unfold unitOn at w ⊢
    rw [map_zpow]
    exact w

end Level

section Main

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

end Main

end GlobalTheory.SiegPt

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AffineLocusAmple

theorem relAmple_of_affine_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ s : LB.Sec M, IsAffineOpen (Out.nonzeroLocus s) → (∀ p : Sp R, ∃ x ∈ Out.nonzeroLocus s, A.hom x = p) → Out.RelAmple A M := by
  intro R _ _ A _ hA M hM s hV hs
  have := hA.proper
  have := hA.smooth
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K _ _ y => ?_
  obtain ⟨n, a, ha⟩ := GlobalTheory.T.exists_finite_translates_cover_geometric_fibre (Sp R) A hA _ K y fun z => hs (y z)
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Sp K))
  have h := GlobalTheory.T.isAmple_lineBundle_pullback_of_translates R A hA M hM _ _ rfl hV ⟨M, hM, s, rfl, rfl⟩ (Over.mk y) n a ha
    fun i => GlobalTheory.cechPic_sp_field_eq_zero K _
  exact h

end GlobalTheory.AffineLocusAmple
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TorsGeomPow

theorem pow_eq_one_of_geometric_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left),
      ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  intro S A _ hA n hn T x hx d hpt
  obtain ⟨-, -, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  set P : Over S := pullback (mulN A n) (η : 𝟙_ (Over S) ⟶ A) with hP
  have hPe : Etale P.hom := hZe
  have hxd : (x ^ d) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, ← pow_mul, mul_comm, pow_mul, hx, one_pow, CategoryTheory.Hom.one_def]
  have h1 : (1 : T ⟶ A) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, one_pow, CategoryTheory.Hom.one_def]
  let y₁ : T ⟶ P := pullback.lift (x ^ d) (toUnit T) hxd
  let u₁ : T ⟶ P := pullback.lift 1 (toUnit T) h1
  have hy : y₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = x ^ d := pullback.lift_fst _ _ _
  have hu : u₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = 1 := pullback.lift_fst _ _ _
  have key : ∀ {W : Over S} (f : W ⟶ T), (f ≫ x) ^ d = 1 → f ≫ y₁ = f ≫ u₁ := by
    intro W f hf
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hy, hu, MonObj.comp_pow, hf, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hyu : y₁ = u₁ := by
    haveI := hPe
    have hw : y₁.left ≫ P.hom = u₁.left ≫ P.hom := by rw [Over.w, Over.w]
    let l : T.left ⟶ pullback P.hom P.hom := pullback.lift _ _ hw
    have hl1 : l ≫ pullback.fst _ _ = y₁.left := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd _ _ = u₁.left := pullback.lift_snd _ _ _
    have hs : Function.Surjective (pullback.snd (pullback.diagonal P.hom) l) := by
      intro s
      let k := AlgebraicClosure (T.left.residueField s)
      let ξ : Sp k ⟶ T.left :=
        Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField s) k)) ≫ T.left.fromSpecResidueField s
      have hξ : ξ ≫ y₁.left = ξ ≫ u₁.left :=
        congrArg CommaMorphism.left (key (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) (hpt k ξ))
      have hq : (ξ ≫ y₁.left) ≫ pullback.diagonal P.hom = ξ ≫ l := by
        apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [pullback.diagonal_fst, Category.comp_id, hl1]
        · simp only [Category.assoc]
          rw [pullback.diagonal_snd, Category.comp_id, hl2, hξ]
      refine ⟨pullback.lift _ _ hq (IsLocalRing.closedPoint k), ?_⟩
      have e : (pullback.lift _ _ hq ≫ pullback.snd (pullback.diagonal P.hom) l) (IsLocalRing.closedPoint k) =
          ξ (IsLocalRing.closedPoint k) := by rw [Limits.pullback.lift_snd]
      refine (Eq.trans ?_ e).trans ?_
      · rfl
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply s _)
    have : Epi (pullback.snd (pullback.diagonal P.hom) l).base :=
      (TopCat.epi_iff_surjective _).2 hs
    have : IsIso (pullback.snd (pullback.diagonal P.hom) l) := IsOpenImmersion.isIso _
    have hl : l = inv (pullback.snd (pullback.diagonal P.hom) l) ≫ pullback.fst _ _ ≫
        pullback.diagonal P.hom := by
      rw [pullback.condition, IsIso.inv_hom_id_assoc]
    apply Over.OverMorphism.ext
    rw [← hl1, ← hl2, hl]
    simp
  rw [← hy, hyu, hu]

end GlobalTheory.TorsGeomPow
end
end

section

set_option autoImplicit false

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open NumberField

namespace GlobalTheory

namespace TraceTensor

variable {E : Type} [Field E] [NumberField E]

theorem exists_integral_orthogonal (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (e : Module.Basis (Fin n) ℚ E), (∀ i, e i = (b i : E)) ∧
      ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0 := by
  classical
  let B : LinearMap.BilinForm ℚ E := (Algebra.traceForm ℚ E).comp σ.toLinearMap LinearMap.id
  have hB : ∀ x y, B x y = Algebra.trace ℚ E (σ x * y) := fun _ _ => rfl
  have hs : LinearMap.IsSymm B := ⟨fun x y => by
    rw [RingHom.id_apply, hB, hB, ← Algebra.trace_eq_of_algEquiv σ, map_mul, hσ, mul_comm]⟩
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hint : ∀ y : E, ∃ (m : ℕ) (b : 𝓞 E), m ≠ 0 ∧ (m : ℚ) • y = (b : E) := by
    intro y
    have halg : IsAlgebraic ℤ y :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, b, hm, hb⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    exact ⟨m, b, hm, by rw [Nat.cast_smul_eq_nsmul, hb]⟩
  choose m b hm hb using hint
  have hu : ∀ i, IsUnit ((m (e i) : ℕ) : ℚ) := fun i => IsUnit.mk0 _ (Nat.cast_ne_zero.2 (hm _))
  refine ⟨_, fun i => b (e i), e.isUnitSMul hu, fun i => ?_, fun i j hij => ?_⟩
  · rw [Module.Basis.isUnitSMul_apply, hb]
  · have h : Algebra.trace ℚ E (σ (e i) * e j) = 0 := he hij
    rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply, Rat.smul_def (m (e i) : ℚ), map_mul σ,
      map_ratCast, ← Rat.smul_def, smul_mul_assoc,
      mul_smul_comm, map_smul, map_smul, h, smul_zero, smul_zero]

theorem trace_mul_eq_repr (σ : E ≃ₐ[ℚ] E) {ι : Type} [Fintype ι] (e : Module.Basis ι ℚ E)
    (ho : ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0) (y : E) (i : ι) :
    Algebra.trace ℚ E (σ (e i) * y) = e.repr y i * Algebra.trace ℚ E (σ (e i) * e i) := by

  conv_lhs => rw [← e.sum_repr y, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [mul_smul_comm, map_smul, smul_eq_mul]
  · intro j _ hj
    rw [mul_smul_comm, map_smul, ho i j hj.symm, smul_zero]
  · simp

end TraceTensor


open TraceTensor in
theorem exists_cm_trace_tensor : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (n c : ℕ) (b : Fin n → NumberField.RingOfIntegers E) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c ∧ (∀ s t, T s t = T t s) ∧ (∀ (a : NumberField.RingOfIntegers E) (g : NumberField.RingOfIntegers E →ₗ[ℤ] NumberField.RingOfIntegers E →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * H.bar a)) ∧ ∑ s, ∑ t, T s t • (H.bar (b s) * b t) = (c : NumberField.RingOfIntegers E) ∧ ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t := by
  intro E _ _ _ H
  classical
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have hbar : ∀ x : 𝓞 E, ((H.bar x : 𝓞 E) : E) = σ (x : E) := fun x => H.bar_eq x
  obtain ⟨n, b, e, heb, ho⟩ := exists_integral_orthogonal σ hσσ
  have htr : ∀ x y : 𝓞 E, ((Algebra.trace ℤ (𝓞 E) (H.bar x * y) : ℤ) : ℚ)
      = Algebra.trace ℚ E (σ (x : E) * (y : E)) := by
    intro x y
    rw [Algebra.coe_trace_int, ← hbar]
    rfl
  let d : Fin n → ℤ := fun i => Algebra.trace ℤ (𝓞 E) (H.bar (b i) * b i)
  have hdq : ∀ i, (d i : ℚ) = Algebra.trace ℚ E (σ (e i) * e i) := fun i => by
    rw [heb]; exact htr _ _
  have hdq0 : ∀ i, 0 < Algebra.trace ℚ E (σ (e i) * e i) := fun i =>
    StarNormBound.trace_conj_mul_pos _ (e.ne_zero i)
  have hd : ∀ i, 0 < d i := fun i => by
    have := hdq0 i
    rw [← hdq] at this
    exact_mod_cast this
  let t : Fin n → ℤ := fun i => ∏ j ∈ Finset.univ.erase i, d j
  let C : ℤ := ∏ j, d j
  have hC : 0 < C := Finset.prod_pos fun j _ => hd j
  have ht : ∀ i, 0 < t i := fun i => Finset.prod_pos fun j _ => hd j
  have htd : ∀ i, d i * t i = C := fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have htq : ∀ i, (t i : ℚ) = C * (Algebra.trace ℚ E (σ (e i) * e i))⁻¹ := fun i => by
    rw [← hdq, ← htd i]
    have : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    push_cast
    field_simp
  have hexp : ∀ x : 𝓞 E, C • x = ∑ j, (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * x)) • b j := by
    intro x
    apply RingOfIntegers.coe_injective

    rw [map_zsmul, map_sum]
    have hx := e.sum_repr (x : E)
    change C • (x : E) = _
    conv_lhs => rw [← hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    change _ = _ • (b j : E)
    rw [← heb, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_mul, htr, ← heb, trace_mul_eq_repr σ e ho, htq]
    have := (hdq0 j).ne'
    field_simp
  have hsym : ∀ x y a : 𝓞 E, Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a))
      = Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) := by
    intro x y a
    have : ((Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a)) : ℤ) : ℚ)
      = ((Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) : ℤ) : ℚ) := by
      rw [htr, htr, ← Algebra.trace_eq_of_algEquiv σ]
      congr 1
      have h1 : ((y * H.bar a : 𝓞 E) : E) = (y : E) * σ (a : E) := by rw [← hbar]; rfl
      have h2 : ((x * a : 𝓞 E) : E) = (x : E) * (a : E) := rfl
      rw [h1, h2, map_mul, map_mul, hσσ, hσσ]
      ring
    exact_mod_cast this
  refine ⟨n, C.toNat, b, Matrix.diagonal t, by omega, fun s u => ?_, fun a g => ?_, ?_, fun v hv => ?_⟩
  · by_cases h : s = u
    · rw [h]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    apply mul_left_cancel₀ hC.ne'
    have h1 : ∀ i, C * (t i * g (b i * a) (b i)) =
        ∑ j, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro i
      have : C * g (b i * a) (b i) = g (C • (b i * a)) (b i) := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

      rw [mul_left_comm, this, hexp, map_sum, LinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ j, C * (t j * g (b j) (b j * H.bar a)) =
        ∑ i, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro j
      have : C * g (b j) (b j * H.bar a) = g (b j) (C • (b j * H.bar a)) := by
        rw [map_smul, smul_eq_mul]

      rw [mul_left_comm, this, hexp, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, hsym]
      ring
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [h1, h2]
    exact Finset.sum_comm
  · simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hc := StarNormBound.casimir σ e ho fun i => (hdq0 i).ne'
    apply RingOfIntegers.coe_injective

    rw [map_sum, map_natCast, ← Int.cast_natCast, Int.toNat_of_nonneg hC.le, ← mul_one (C : E), ← hc,
    Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_mul]
    change t i • (((H.bar (b i) : 𝓞 E) : E) * (b i : E)) = _
    rw [hbar, ← heb, ← Int.cast_smul_eq_zsmul ℚ, htq, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rw [mul_assoc]; exact mul_nonneg (ht j).le (mul_self_nonneg _)
    · rw [mul_assoc]; exact mul_pos (ht i) (mul_self_pos.2 hi)

end GlobalTheory
end
