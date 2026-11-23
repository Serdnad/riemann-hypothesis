module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RetractPullback

theorem exists_isGrpPullback_of_retracts : ∀ {S S' B : Scheme.{0}} (j : S' ⟶ S) (f : S' ⟶ B) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (P : Over B) [GrpObj P] (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback G' P f ψ) (e : G ⟶ G) (e₀ : P ⟶ P) (e' : G' ⟶ G') (he' : IsMonHom e') (h₁ : e'.left ≫ φ = φ ≫ e.left) (h₂ : e'.left ≫ ψ = ψ ≫ e₀.left) (H : Over S) [GrpObj H] (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = e) (C : Over B) [GrpObj C] (k : C ⟶ P) (p : P ⟶ C) (hk : IsMonHom k) (hp : IsMonHom p) (hkp : k ≫ p = 𝟙 C) (hpk : p ≫ k = e₀), ∃ (C' : Over S') (_ : GrpObj C') (a : C'.left ⟶ H.left) (b : C'.left ⟶ C.left), IsGrpPullback C' H j a ∧ IsGrpPullback C' C f b := by
  intro S S' B j f G _ G' _ P _ φ ψ hφ hψ e e₀ e' he' h₁ h₂ H _ i r hi hr hir hri C _ k p hk hp hkp hpk
  have hb := isGrpPullback_pullback C f
  have wk : k.left ≫ P.hom = C.hom := Over.w k
  have wp : p.left ≫ C.hom = P.hom := Over.w p
  have wi : i.left ≫ G.hom = H.hom := Over.w i
  have wr : r.left ≫ H.hom = G.hom := Over.w r
  have we' : e'.left ≫ G'.hom = G'.hom := Over.w e'
  have kp : k.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hkp]; rfl
  have pk : p.left ≫ k.left = e₀.left := by rw [← Over.comp_left, hpk]
  have ir : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir]; rfl
  have ri : r.left ≫ i.left = e.left := by rw [← Over.comp_left, hri]
  have hmw : (pullback.fst C.hom f ≫ k.left) ≫ P.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, wk]; exact pullback.condition
  let m : pullback C.hom f ⟶ G'.left := hψ.1.lift (pullback.fst C.hom f ≫ k.left) (pullback.snd C.hom f) hmw
  have mψ : m ≫ ψ = pullback.fst C.hom f ≫ k.left := hψ.1.lift_fst _ _ _
  have mh : m ≫ G'.hom = pullback.snd C.hom f := hψ.1.lift_snd _ _ _
  have fix : ∀ {T : Scheme.{0}} (x : T ⟶ pullback C.hom f), x ≫ m ≫ e'.left = x ≫ m := by
    intro T x
    apply hψ.1.hom_ext
    · simp only [Category.assoc, h₂, reassoc_of% mψ, mψ, ← pk, reassoc_of% kp]
    · simp only [Category.assoc, we']
  refine ⟨(Over.pullback f).obj C, inferInstance, m ≫ φ ≫ r.left, pullback.fst C.hom f, ⟨?_, ?_⟩, hb⟩
  · have comm : (m ≫ φ ≫ r.left) ≫ H.hom = pullback.snd C.hom f ≫ j := by
      rw [Category.assoc, Category.assoc, wr, hφ.1.w, reassoc_of% mh]
    refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm (fun s => pullback.lift
        (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left) s.snd
        (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc])) ?_ ?_ ?_⟩⟩
    · intro s
      have hm : pullback.lift (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left)
          s.snd (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc]) ≫ m =
          hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ e'.left := by
        apply hψ.1.hom_ext
        · simp only [Category.assoc, mψ, h₂, pullback.lift_fst_assoc, pk]
        · simp only [Category.assoc, mh, we', pullback.lift_snd, hφ.1.lift_snd]
      rw [reassoc_of% hm, reassoc_of% h₁, hφ.1.lift_fst_assoc, ← ri]
      simp only [Category.assoc, reassoc_of% ir, ir, Category.comp_id]
    · intro s
      exact pullback.lift_snd _ _ _
    · intro s n hn1 hn2
      have hx : n ≫ m = hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) := by
        apply hφ.1.hom_ext
        · rw [hφ.1.lift_fst, ← hn1]
          calc (n ≫ m) ≫ φ = n ≫ m ≫ e'.left ≫ φ := by rw [reassoc_of% (fix n), Category.assoc]
            _ = _ := by rw [h₁, ← ri]; simp only [Category.assoc]
        · rw [hφ.1.lift_snd, Category.assoc, mh]; exact hn2
      apply pullback.hom_ext
      · rw [pullback.lift_fst, ← reassoc_of% hx, reassoc_of% mψ, kp, Category.comp_id]
      · rw [pullback.lift_snd]; exact hn2
  · intro T x y x₀ y₀ hx hy
    let M : (Over.pullback f).obj C ⟶ G' := Over.homMk m mh
    have pt : ∀ z : T ⟶ (Over.pullback f).obj C, pushPt hψ.1.w (z ≫ M) = pushPt hb.1.w z ≫ k :=
      fun z => Over.OverMorphism.ext (by
        show (z.left ≫ m) ≫ ψ = (z.left ≫ pullback.fst C.hom f) ≫ k.left
        rw [Category.assoc, mψ, Category.assoc])
    have Mmul : (x * y) ≫ M = (x ≫ M) * (y ≫ M) := by
      apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have e1 := hb.2 T x y (pushPt hb.1.w x) (pushPt hb.1.w y) rfl rfl
        have e2 := hψ.2 T (x ≫ M) (y ≫ M) (pushPt hψ.1.w (x ≫ M)) (pushPt hψ.1.w (y ≫ M)) rfl rfl
        rw [← e2, pt, pt, ← MonObj.mul_comp]
        show ((x * y).left ≫ m) ≫ ψ = (pushPt hb.1.w x * pushPt hb.1.w y).left ≫ k.left
        rw [e1, Category.assoc, mψ, Category.assoc]
      · rw [Over.w ((x * y) ≫ M), Over.w ((x ≫ M) * (y ≫ M))]
    have ex : x₀ = pushPt hφ.1.w (x ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hx]; show _ = ((x.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have ey : y₀ = pushPt hφ.1.w (y ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hy]; show _ = ((y.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have e3 := hφ.2 T (x ≫ M) (y ≫ M) (pushPt hφ.1.w (x ≫ M)) (pushPt hφ.1.w (y ≫ M)) rfl rfl
    rw [ex, ey, ← MonObj.mul_comp, Over.comp_left, e3, ← Mmul]
    show ((x * y).left ≫ m) ≫ φ ≫ r.left = _
    simp only [Category.assoc]

end GlobalTheory.RetractPullback
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isMonHom_of_isGrpPullback_fst {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (bc : G' ≅ (Over.pullback s).obj G) (h : IsGrpPullback G' G s (bc.hom.left ≫ pullback.fst G.hom s)) :
    IsMonHom bc.hom := by
  obtain ⟨e, me, he⟩ := grpPullback_iso h (isGrpPullback_pullback G s)
  have : e.hom = bc.hom := Over.OverMorphism.ext (pullback.hom_ext he ((Over.w e.hom).trans (Over.w bc.hom).symm))
  exact this ▸ me

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  first | exact @GlobalTheory.SymGrpPull.symm_pull | exact GlobalTheory.SymGrpPull.symm_pull | (intros; apply GlobalTheory.SymGrpPull.symm_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pow_eq_one_of_isGrpPullback_of_injective : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → ∀ (x : baseOver (Sp Ω) ⟶ A.A) (y : baseOver (Sp T) ⟶ P.A) (k : ℕ), x.left ≫ φ = spMap jT ≫ y.left → x ^ k = 1 → y ^ k = 1 := by
  intro Ω T _ _ _ jT hj A P φ hφ x y k hxy hx
  let U : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have e1 : pushHom hφ (baseOver (Sp Ω)) x = U ≫ y := Over.OverMorphism.ext hxy
  have e2 : U ≫ y ^ k = U ≫ 1 :=
    calc U ≫ y ^ k = preHom U (y ^ k) := rfl
      _ = (preHom U y) ^ k := map_pow _ _ _
      _ = (pushHom hφ (baseOver (Sp Ω)) x) ^ k := by rw [e1]; rfl
      _ = pushHom hφ (baseOver (Sp Ω)) (x ^ k) := (map_pow _ _ _).symm
      _ = 1 := by rw [hx, map_one]
      _ = preHom U 1 := (map_one _).symm
  have e3 : spMap jT ≫ (y ^ k).left = spMap jT ≫ (1 : baseOver (Sp T) ⟶ P.A).left :=
    congrArg (fun z => z.left) e2
  have : IsDominant (spMap jT) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical jT).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot jT).1 hj]; exact bot_le)⟩
  have := P.isAb.proper
  have : IsReduced (baseOver (Sp T)).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of T)))
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P.A.hom
    ((Over.w (y ^ k)).trans (Over.w (1 : baseOver (Sp T) ⟶ P.A)).symm) (spMap jT) e3)

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (j : B →+* C) :
    spMap j ≫ spMap f = spMap (j.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem isThetaPt_fibre : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (m : ℕ) (I : Type) (x : I → (baseOver (Sp Ω) ⟶ A.A)) (y : I → (baseOver (Sp T) ⟶ P.A)) (v : I → F), Odd m → 3 ≤ m → (∀ i, (x i).left ≫ φ = spMap jT ≫ (y i).left) → (∀ i, y i ^ (m ^ 2) = 1) → (∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ m = 1 → ∃ i, ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) ^ m = z) → IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → IsThetaPt P m (fun i => (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v i)) := by
  intro F Ω T _ _ _ _ _ _ _ _ em jT t hft hinj hcomp A P φ hp hw m I x y v hm hm3 hxy hy hcov hA
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  let tR : T →+* F := t.toRingHom
  have htR : ∀ a : F, tR (algebraMap F T a) = a := fun a => t.commutes a
  have hsurj : Function.Surjective tR := fun a => ⟨algebraMap F T a, htR a⟩
  let p : Ideal T := RingHom.ker tR
  haveI hpm : p.IsMaximal := RingHom.ker_isMaximal_of_surjective tR hsurj
  let R := Localization.AtPrime p
  let s : Sp R ⟶ Sp T := spMap (algebraMap T R)
  have hjT : ∀ z : p.primeCompl, IsUnit (jT z) := fun z => by
    refine IsUnit.mk0 _ fun h => z.2 ?_
    have : (z : T) = 0 := hinj (h.trans (map_zero jT).symm)
    rw [this]; exact p.zero_mem
  have htU : ∀ z : p.primeCompl, IsUnit (tR z) := fun z => IsUnit.mk0 _ fun h => z.2 h
  let jR : R →+* Ω := IsLocalization.lift hjT
  let r : R →+* F := IsLocalization.lift htU
  have hjR : jR.comp (algebraMap T R) = jT := IsLocalization.lift_comp hjT
  have hr : r.comp (algebraMap T R) = tR := IsLocalization.lift_comp htU
  have hjRinj : Function.Injective jR := by
    refine (injective_iff_map_eq_zero jR).2 fun z hz => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have hz' := hz
    simp only [jR] at hz'
    rw [IsLocalization.lift_mk', Units.mul_left_eq_zero] at hz'
    show IsLocalization.mk' R a b = 0
    rw [hinj (hz'.trans (map_zero jT).symm), IsLocalization.mk'_zero]
  let aR : F →+* R := (algebraMap T R).comp (algebraMap F T)
  have hjaR : ∀ a, jR (aR a) = em a := fun a => by
    show (jR.comp (algebraMap T R)) (algebraMap F T a) = em a
    rw [hjR, ← hcomp]; rfl
  have hraR : ∀ a, r (aR a) = a := fun a => by
    show (r.comp (algebraMap T R)) (algebraMap F T a) = a
    rw [hr]; exact htR a
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu : IsUnit (m : R) := by
    have := (IsUnit.mk0 (m : F) hmF).map aR
    rwa [map_natCast] at this

  have hmo : ∀ i, ((Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i) ^ (m ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨w, hwR⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local hL hL2 P s hm hu _ hmo

  have e1 : spMap jR ≫ s = 𝟙 (Sp Ω) ≫ spMap jT := by
    rw [Category.id_comp, spMap_comp_spMap, hjR]
  have e2 : spMap r ≫ s = spMap tR := by rw [spMap_comp_spMap, hr]
  have hΩ := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P jR e1 hwR
  have hF := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P r e2 hwR

  let yΩ : I → (Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ P.A) := fun i =>
    (Over.homMk (spMap jR) e1 : Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ Over.mk s) ≫
      (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i
  have hyΩ : ∀ i, (yΩ i).left = (x i).left ≫ φ := fun i => by
    rw [hxy i]
    simp only [yΩ, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, e1, Category.id_comp]
  obtain ⟨eA, heA⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp Ω)) (𝟙 (Sp Ω) ≫ spMap jT) rfl
  have hxo : ∀ i, x i ^ (m ^ 2) = 1 := fun i => by
    apply eA.injective
    rw [map_pow, map_one]
    have : eA (x i) = yΩ i := Over.OverMorphism.ext ((heA (x i)).trans (hyΩ i).symm)
    rw [this]
    simp only [yΩ]
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hy, MonObj.comp_one, MonObj.comp_one]
  have hA' := (GlobalTheory.ThetaPtUp.isThetaPt_iff (T := baseOver (Sp Ω)) (x₀ := yΩ) hp hw hyΩ hxo _).1 hA
  let eΩ : Γ(Sp Ω, ⊤) ≃+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk (𝟙 (Sp Ω) ≫ spMap jT)).left, ⊤) := eΩ.symm.isLocalRing
  obtain ⟨u, hu'⟩ := GlobalTheory.ThetaUniq.exists_unit_over hL.globalFns P hm
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hΩ) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hA')
  let cΩ : Ωˣ := Units.map eΩ.toMonoidHom u
  have hc : ∀ i, em (v i) = (cΩ : Ω) * jR (w i) := fun i =>
    (eΩ.apply_symm_apply (em (v i))).symm.trans (((congrArg eΩ (hu' i)).trans (map_mul eΩ _ _)).trans
      (congrArg (_ * ·) (eΩ.apply_symm_apply (jR (w i)))))

  have hF' : IsThetaPt P m (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i)
      (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i))) := by
    have hpts : (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i) =
        fun i => (Over.homMk (spMap r) e2 : Over.mk (spMap tR) ⟶ Over.mk s) ≫
          (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i := funext fun i => by
      refine Over.OverMorphism.ext ?_
      simp only [Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, e2]
    rw [hpts]
    exact hF
  obtain ⟨z, hz, hne⟩ := GlobalTheory.ThetaCoset.exists_ne_zero_over hL hL2 P (spMap tR) (k := m) (by omega) hmF
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hF') 1
  obtain ⟨i₀, hi₀⟩ := hcov z hz
  have hr0 : r (w i₀) ≠ 0 := fun h => hne i₀ (by rw [_root_.one_mul]; exact hi₀) (by
    show (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i₀)) = 0
    rw [h]; exact map_zero _)

  have hv0 : v i₀ ≠ 0 := fun h => hr0 (by
    have q := hc i₀
    rw [h, map_zero, eq_comm, Units.mul_right_eq_zero] at q
    rw [hjRinj (q.trans (map_zero jR).symm), map_zero])
  have key : ∀ i, w i * aR (v i₀) = w i₀ * aR (v i) := fun i => hjRinj (by
    rw [map_mul, map_mul, hjaR, hjaR, hc, hc]; ring)
  have hrw : ∀ i, r (w i) * v i₀ = r (w i₀) * v i := fun i => by
    have q := congrArg r (key i)
    rwa [map_mul, map_mul, hraR, hraR] at q
  have hd : r (w i₀) / v i₀ ≠ 0 := div_ne_zero hr0 hv0
  have hfin : ∀ i, (r (w i₀) / v i₀)⁻¹ * r (w i) = v i := fun i => by
    rw [inv_div, div_mul_eq_mul_div, div_eq_iff hr0]
    linear_combination hrw i
  have H := GlobalTheory.Ex.Specialise.isThetaPt_mul P hF' (inv_ne_zero hd)
  simp only [hfin] at H
  exact H

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifAdjoint

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cubeLB_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin a
  obtain ⟨hno, -, hic, -⟩ := hR
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  have ha := oG.hom a
  have hsa := oG.hom (star a)
  have hgen := U.gen_hom
  have hL := U.LG.isLB
  have hA := A.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance
  have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩

  have eA : cubeCls A.A ![fst A.A A.A ≫ oA.act a, snd A.A A.A] (cls A.L hA) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] (cls A.L hA) :=
    (cls_cubeLB A.A _ hA).symm.trans (((cls_eq_iff (LB.isLB_linComb hA _ _) (LB.isLB_linComb hA _ _)).2
      (GlobalTheory.FullPoint.lbIso_of_rosatiAdj hA (oA.rosati a))).trans (cls_cubeLB A.A _ hA))
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
      CechPic.pull U.gen.hom.left (cls A.L hA) := by
    obtain ⟨w, hw⟩ := U.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm

  have hgK : cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act a),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) =
      cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act (star a))]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) := by
    rw [hc']
    let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
      (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
    have hu : u.left ≫ (A.A ⊗ A.A).hom = ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e₁ := hlin.ext a
    have e₂ := hlin.ext (star a)
    rw [← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A ≫ oA.act a, snd A.A A.A] u.left hu (fun i => ?_),
      ← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] u.left hu
        (fun i => ?_), eA]
    · fin_cases i
      · show (fst _ _ ≫ U.gen.hom).left = (u ≫ fst A.A A.A).left
        congr 1; simp [u]
      · show ((snd _ _ ≫ (Over.pullback (jK R)).map (oG.act (star a))) ≫ U.gen.hom).left = (u ≫ snd A.A A.A ≫ oA.act (star a)).left
        congr 1; simp [u, e₂]
    · fin_cases i
      · show ((fst _ _ ≫ (Over.pullback (jK R)).map (oG.act a)) ≫ U.gen.hom).left = (u ≫ fst A.A A.A ≫ oA.act a).left
        congr 1; simp [u, e₁]
      · show (snd _ _ ≫ U.gen.hom).left = (u ≫ snd A.A A.A).left
        congr 1; simp [u]
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  refine pic_ext (jK R) hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
  · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
      (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
    fin_cases i <;> simp
  · have hGp := isGrpPullback_pullback G (jK R)
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    let δ := lift ((Over.pullback (jK R)).map (fst G G)) ((Over.pullback (jK R)).map (snd G G))
    have e := congrArg (CechPic.pull δ.left) hgK
    have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hGp (T' := (Over.pullback (jK R)).obj (G ⊗ G)) (T := G ⊗ G)
      (fun i => (Over.pullback (jK R)).map (x i)) x (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    rw [pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G ≫ oG.act a, snd G G] i)) δ
        (fun i => by fin_cases i <;> simp [δ]),
      pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G, snd G G ≫ oG.act (star a)] i)) δ
        (fun i => by fin_cases i <;> simp [δ])] at e
    exact (e' _).trans (e.trans (e' _).symm)

end GlobalTheory.Mum.UnifAdjoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1 := by
  first | (exact @GlobalTheory.WeilSqKer.weilIs_eq_one) | (exact GlobalTheory.WeilSqKer.weilIs_eq_one) | (intros; apply GlobalTheory.WeilSqKer.weilIs_eq_one  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | exact GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample | (intros; apply GlobalTheory.PrimitiveNonSym.exists_point_translate_of_ample <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  first | exact @GlobalTheory.SymTranslate.exists_sym_translate | exact GlobalTheory.SymTranslate.exists_sym_translate | (intros; apply GlobalTheory.SymTranslate.exists_sym_translate <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_isGrpPullback_of_compatible_retracts : ∀ {S S' B : Scheme.{0}} (j : S' ⟶ S) (f : S' ⟶ B) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (P : Over B) [GrpObj P] (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback G' P f ψ) (e : G ⟶ G) (e₀ : P ⟶ P) (e' : G' ⟶ G') (he' : IsMonHom e') (h₁ : e'.left ≫ φ = φ ≫ e.left) (h₂ : e'.left ≫ ψ = ψ ≫ e₀.left) (H : Over S) [GrpObj H] (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = e) (C : Over B) [GrpObj C] (k : C ⟶ P) (p : P ⟶ C) (hk : IsMonHom k) (hp : IsMonHom p) (hkp : k ≫ p = 𝟙 C) (hpk : p ≫ k = e₀), ∃ (C' : Over S') (_ : GrpObj C') (a : C'.left ⟶ H.left) (b : C'.left ⟶ C.left), IsGrpPullback C' H j a ∧ IsGrpPullback C' C f b := by
  first | exact @GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts | exact GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts | (intros; apply GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts <;> assumption)

end
end
