module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryBranchesDistinctPrimesToricChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianActionEqUniversalAtFieldPointsOfTheta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevSpread

theorem eq_of_comp_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Z : Over S) [PreconnectedSpace Z.left] (x y : Z ⟶ A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (T : Over S) (z : T ⟶ Z) [Nonempty T.left] (h : z ≫ x = z ≫ y) : x = y := by
  have hw : (x * y⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, _root_.mul_one]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one A hA hn (x * y⁻¹) hw
  have h1 : z ≫ (x * y⁻¹) = 1 := by
    show (preHom z) (x * y⁻¹) = 1
    rw [map_mul, map_inv]
    show (z ≫ x) * (z ≫ y)⁻¹ = 1
    rw [h, mul_inv_cancel]
  have hsub := (hz T z).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 Z ≫ (x * y⁻¹) = 1 := (hz Z (𝟙 Z)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LevSpread

namespace GlobalTheory.LevSpread

theorem l1 : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := GlobalTheory.T.grpPullback_of_sameFibreWithSquareBundle

theorem l2a : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := GlobalTheory.T.exists_torsionSection_of_torsionRationalOverFraction

theorem l2 : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R₀ _ _ _ _ A _ _ n hA hnR hT K _ t x hx
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this
  let t' : Sp (AlgebraicClosure K) ⟶ Sp R₀ := spMap (algebraMap K (AlgebraicClosure K)) ≫ t
  let z : Over.mk t' ⟶ Over.mk t := Over.homMk (spMap (algebraMap K (AlgebraicClosure K))) rfl
  obtain ⟨σ, hσ, hσx⟩ := l2a R₀ A n hA hnR hT (AlgebraicClosure K) t' (z ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  refine ⟨σ, hσ, ?_⟩
  haveI : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
  haveI : Nonempty (Over.mk t').left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  refine eq_of_comp_eq A hA hnΓ (Over.mk t) _ x (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one]) hx (Over.mk t') z ?_
  rw [← Category.assoc, show z ≫ toUnit (Over.mk t) = toUnit (Over.mk t') from toUnit_unique _ _, hσx]

theorem l3 : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := GlobalTheory.T.weilPairing_eq_zpow_of_fieldPoint_domain

theorem prim_map {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] [IsDomain R] (β : cycAway n →+* R) :
    IsPrimitiveRoot (β (zetaAway n)) n := by
  have h₁ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective
  have : NeZero (n : R) := ⟨by simpa using ((isUnit_natCast hn).map β).ne_zero⟩
  have h₂ := (h₁.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h₂

theorem level_spreads : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (b : cycAway n →+* R₀) (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → IsPPol A P → TorsRat A n → ∀ (g : ℕ) (K : Type) [Field K] (κ : R₀ →+* K) (c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b))), c₀.Principal → SameFib c₀.A c₀.P (𝟙 _) A P (spMap κ) → ∃ c : SiegPre g n (zetaAway n) (spMap b), c.Principal ∧ SiegPB c₀ c (spMap κ) ∧ ∃ (a : c.A.left ⟶ A.left) (a₂ : (G2 c.A).left ⟶ (G2 A).left), IsGrpPullback c.A A (𝟙 _) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂) := by
  intro n hn3 hnodd R₀ _ _ _ _ b A _ _ P hA hP hT g K _ κ c₀ hc₀ hsf
  have hn0 : n ≠ 0 := by omega
  have hnR : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map b
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  have hζU : (ζU : cycAway n) = zetaAway n := rfl
  let ζR : R₀ˣ := Units.map b.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (prim_map hn0 b)

  obtain ⟨φ, φ₂, hφ, hsq, hiso, hdiag⟩ := l1 _ _ c₀.A c₀.P A P (spMap κ) c₀.isLB hP.1.1 hsf
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  have hxa : ∀ a, (E (c₀.lev a)) ^ n = 1 := fun a => by rw [← map_pow, c₀.lev_tors, map_one]
  choose σ hσn hσx using fun a => l2 R₀ A n hA hnR hT K _ (E (c₀.lev a)) (hxa a)
  have hcomp : ∀ a, (c₀.lev a).left ≫ φ = spMap κ ≫ (σ a).left := fun a => by
    have e := congrArg (fun w => w.left) (hσx a)
    simp only [Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at e
    rw [← GlobalTheory.ObjPull.pushEquiv_left hφ, ← e]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp R₀))).left := inferInstanceAs (PreconnectedSpace (Sp R₀))
  have inj : ∀ (T : Over (Sp R₀)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp R₀)) ⟶ A), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    eq_of_comp_eq A hA hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap κ)).left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj _ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c₀.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp R₀)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩
  let c : SiegPre g n (zetaAway n) (spMap b) :=
    { A := A
      ab := hA
      P := P
      isLB := hP.1.1
      rig₁ := hP.1.2.1
      rig₂ := hP.1.2.2.1
      symm := hP.1.2.2.2
      lev := σ
      lev_add := hadd
      lev_tors := hσn
      geom := ?_ }
  refine ⟨c, ⟨hP.2.1, hP.2.2⟩, ⟨φ, φ₂, hφ, hsq, hiso, hcomp⟩,
    ⟨𝟙 _, 𝟙 _, isGrpPullback_self A, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩, GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP.1.1⟩⟩
  intro k _ _ x β z hxβ hz
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R₀ →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp b := by
    have e : spMap (ρ.comp b) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c₀.geom (AlgebraicClosure K) x₀ ((iK.comp κ).comp b)
    (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp R₀) := Over.mk ((Over.mk x₀).hom ≫ spMap κ)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c₀.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  refine ⟨fun a => ?_, fun gg hg => ?_, fun a a' => ?_⟩
  · rw [one_iff, ← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a
  · obtain ⟨τ, hτn, hτ⟩ := l2 R₀ A n hA hnR hT k (spMap ρ) gg hg
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm (toUnit T₀ ≫ τ))
      (by rw [← map_pow, ← MonObj.comp_pow, hτn, MonObj.comp_one, map_one])
    refine ⟨a, ?_⟩
    have e : σ a = τ := inj T₀ _ _ (hσn a) hτn (by rw [← push, ha, MulEquiv.apply_symm_apply])
    rw [e, hτ]
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp R₀) (Sp K) A c₀.A (spMap κ) φ
      (P.pull (lift (𝟙 A) (𝟙 A)).left) (c₀.P.pull (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (pull_isLB hP.1.1 _)
      (pull_isLB c₀.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap κ = spMap (iK.comp κ) := by
      show x₀ ≫ spMap κ = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp κ).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := l3 R₀ A hA P hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR (2 * omegaStd a a')
      (AlgebraicClosure K) (iK.comp κ) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevSpread
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QFEtale

theorem isEtaleCompletion_of_galRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  intro O R _ _ _ _ _ _ _ _ _ _ f _ hRc hqf hfin hdim hrig
  haveI hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  letI : Algebra (ResidueField O) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hres : (residue R).comp f = (ResidueField.map f).comp (residue O) := by
    ext o; simp [ResidueField.map_residue]
  have hfin' : (ResidueField.map f).Finite := by
    rw [hres] at hfin; exact RingHom.Finite.of_comp_finite hfin
  haveI : Module.Finite (ResidueField O) (ResidueField R) := hfin'
  let M := separableClosure (ResidueField O) (ResidueField R)
  let m : ResidueField O →+* M := algebraMap (ResidueField O) M
  have hmf : m.Finite := RingHom.finite_algebraMap.2 inferInstance
  haveI : Algebra.IsSeparable (ResidueField O) M := inferInstance
  haveI : Algebra.FormallyUnramified (ResidueField O) M := Algebra.FormallyUnramified.of_isSeparable _ _
  have hmu : m.FormallyUnramified := RingHom.formallyUnramified_algebraMap.2 inferInstance
  obtain ⟨A, _, _, _, ψ, hψl, E, hAcn, hψe, hψu, hE⟩ := GlobalTheory.T.exists_etaleCompletion_with_residueField_equiv O M m hmf hmu
  obtain ⟨hAn, hAi, hAc, hA0⟩ := hAcn
  let u' : A →+* ResidueField R := (algebraMap M (ResidueField R)).comp ((E.symm : ResidueField A →+* M).comp (residue A))
  have hu' : ∀ a, u' a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (algebraMap M (ResidueField R)).injective,
      map_eq_zero_iff _ E.symm.injective]
  have hker : RingHom.ker u' = maximalIdeal A := by ext a; exact hu' a
  have hc : (residue R).comp f = u'.comp ψ := by
    ext o
    have h1 := RingHom.congr_fun hE (residue O o)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ResidueField.map_residue] at h1
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ← h1, RingEquiv.symm_apply_apply, m]
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.EtaleCompletionLift.exists_extension O A R (ResidueField R) ψ f u' (residue R) hψe hψu hRc
    inferInstance hker (ker_residue) hc (fun r => residue_surjective _)
  have hbm : ∀ a, b a ∈ maximalIdeal R ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff, ← hu', ← RingHom.comp_apply, hb2]
  haveI hbl : IsLocalHom b := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((hbm a).2 ((mem_maximalIdeal a).2 h)) ha⟩
  have hbfin : b.Finite := by
    refine GlobalTheory.T.ringHom_finite_of_quasiFinite_complete_local A R b hAc (fun p hp h => hqf p hp ?_) ?_
    · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact h
    · refine RingHom.Finite.of_comp_finite (f := ψ) ?_
      rw [RingHom.comp_assoc, hb1]; exact hfin
  have hbinj : Function.Injective b := GlobalTheory.T.injective_of_finite_of_ringKrullDim_le' A R b hbfin ((GlobalTheory.T.ringKrullDim_le_of_isEtaleCompletion' O A ψ hψe).trans hdim)
  obtain ⟨R', _, _, _, θ, hR'cn, hθl, hθi, hθf, hfix⟩ := GlobalTheory.T.exists_completeNormal_galois_cover_of_finite A R b ⟨hAn, hAi, hAc, hA0⟩ hbfin hbinj
  let q := ringExpChar M
  haveI : ExpChar M q := ringExpChar.expChar M
  haveI : ExpChar (ResidueField R) q := expChar_of_injective_algebraMap (algebraMap M (ResidueField R)).injective q
  have hpi : ∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a) := by
    intro x
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem M q x
    obtain ⟨a, ha⟩ := residue_surjective (E y)
    refine ⟨n, a, ?_⟩
    rw [← RingHom.comp_apply, hb2, ← hy]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ha, RingEquiv.symm_apply_apply]
  have hbsurj : Function.Surjective b := by
    intro r
    refine hfix r fun σ hσ hσb => hrig R' θ σ hR'cn hθi hθf hσ (fun o => ?_) (fun r => GlobalTheory.T.ringEquiv_sub_mem_maximalIdeal_of_purelyInsep_residue A R R' b θ q σ hpi hσb r) r
    rw [← hb1]; exact hσb (ψ o)
  have hmapsurj : Function.Surjective (ResidueField.map b) := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hbsurj r
    exact ⟨residue A a, ResidueField.map_residue _ _⟩
  have hres2 : (residue R).comp f = (ResidueField.map b).comp ((residue A).comp ψ) := by
    rw [← hb1]; ext o; simp [ResidueField.map_residue]
  refine ⟨⟨?_, ?_, hfin⟩, ?_⟩
  · rw [← hb1]; exact RingHom.Flat.comp hψe.1 (RingHom.Flat.of_bijective ⟨hbinj, hbsurj⟩)
  · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact map_maximalIdeal_of_surjective b hbsurj
  · rw [hres2]; exact RingHom.FormallyUnramified.comp hψu (RingHom.FormallyUnramified.of_surjective hmapsurj)

end GlobalTheory.QFEtale
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

def FromBaseWith {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type} [CommRing W₀]
    (ιb : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
    (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)) : Prop :=
  IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧
    (∀ a, GlobalTheory.UChart.cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (a b : Q.X) zz (J : (Sp V ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Sp V ⟶ B₀.left) → M₀.ι),
      Good Q.P.L zz J → Good M₀ zz J₀ →
      val (τ₀ a b) (𝟙 (Sp V)) zz J =
        gm (GlobalTheory.UChart.cpt Q (a + b)) zz _
            (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q (a + b) ≫ β), J (GlobalTheory.UChart.cpt Q (a + b)))) *
        (gm (GlobalTheory.UChart.cpt Q a) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q a ≫ β), J (GlobalTheory.UChart.cpt Q a))))⁻¹ *
        (gm (GlobalTheory.UChart.cpt Q b) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q b ≫ β), J (GlobalTheory.UChart.cpt Q b))))⁻¹ *
        gm (GlobalTheory.UChart.cpt Q 0) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q 0 ≫ β), J (GlobalTheory.UChart.cpt Q 0))) *
        val (τ₁ a b) (spMap ιb) zz J₀

theorem fromBase_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type}
    [CommRing W₀] (ιb : W₀ →+* V) :
    GlobalTheory.UChart.FromBase Q τ₀ ιb ↔ ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), FromBaseWith Q τ₀ ιb B₀ M₀ c₀ τ₁ β w :=
  Iff.rfl

abbrev gwx {X' X Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (y : Y)
    (J : (Y ⟶ X') → L'.ι) (J₀ : (Y ⟶ X) → L.ι) (x : Y ⟶ X') : (Y.presheaf.stalk y)ˣ :=
  gw w x y (J₀ (x ≫ F)) (J x)

end GlobalTheory.USep.EvG
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.boundaryBranches_distinct_primes_toricChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTaut C → C.y ≫ j = jK _ ≫ ξ → ξ (closedPoint _) ∉ Set.range j → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) → ∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap (Scheme.stalkClosedPointTo ξ).hom = (Ideal.span {bdParam k m e i'}).comap (Scheme.stalkClosedPointTo ξ).hom → i = i' := by
  first | exact @GlobalTheory.BranchSep.branch_sep | exact GlobalTheory.BranchSep.branch_sep | (intros; apply GlobalTheory.BranchSep.branch_sep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_common_scaling_descends_to_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))) (N : ℕ) (Ix : Type) (T : Ix → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) (a : (Kb R →ₐ[FractionRing R] Kb R) → (Kb R)ˣ), (∀ σ i, ∃ t', SecTw σ (T i) t' ∧ ∀ j, t'.f j = liftFun A.A _ (fnF (Kb R) (a σ).val) * (T i).f j) → ∃ c : (Kb R)ˣ, ∀ i, ∃ Φ : H0 A.L N, ∀ t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N, (∀ j, t''.f j = liftFun A.A _ (fnF (Kb R) c.val) * (T i).f j) → Agree A.L t'' Φ := by
  first | exact @GlobalTheory.Mum.exists_common_scale_descends | exact GlobalTheory.Mum.exists_common_scale_descends | (intros; apply GlobalTheory.Mum.exists_common_scale_descends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  first | exact @GlobalTheory.Mum.eqv_eq_smul | exact GlobalTheory.Mum.eqv_eq_smul | (intros; apply GlobalTheory.Mum.eqv_eq_smul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_affine_chart_thetaSystem_unitary_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  first | exact @GlobalTheory.UPoinc.exists_urechart_affine | exact GlobalTheory.UPoinc.exists_urechart_affine | (intros; apply GlobalTheory.UPoinc.exists_urechart_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_recharting_thetaSystem_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w₀ ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ ∧ ∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (ρ'.pt x).left := by
  first | exact @GlobalTheory.UPoinc.exists_rechart_wit | exact GlobalTheory.UPoinc.exists_rechart_wit | (intros; apply GlobalTheory.UPoinc.exists_rechart_wit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.existsUnique_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (F : Type) [Field F] [Algebra (FractionRing R) F], ∃! s : Fam D F k, F₀.Over s := by
  first | exact @GlobalTheory.Mum.IntFam.existsUnique_over | exact GlobalTheory.Mum.IntFam.existsUnique_over | (intros; apply GlobalTheory.Mum.IntFam.existsUnique_over <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.relatingConstant_mem_traitFractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  first | exact @GlobalTheory.Mum.RatConst.main | exact GlobalTheory.Mum.RatConst.main | (intros; apply GlobalTheory.Mum.RatConst.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.deeper_identification_chain_agrees_generically : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) → ∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left := by
  first | exact @GlobalTheory.UPoinc.tied_chain_generic | exact GlobalTheory.UPoinc.tied_chain_generic | (intros; apply GlobalTheory.UPoinc.tied_chain_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.semiAbelianAction_eq_universal_at_fieldPoints_of_thetaModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ wi : UWit X₁, ∃ (f : 𝓞 E → (out.G ⟶ out.G)) (ψ : wi.G.left ⟶ out.G.left), (∀ a, IsMonHom (f a)) ∧ IsGrpPullback wi.G out.G Y.pt ψ ∧ (∀ (T : Scheme.{0}) (w : T ⟶ wi.G.left), ∃ x' : T ⟶ pullback X₁.ρ.P.A.hom out.u₀, x' ≫ out.φ = w ≫ ψ ∧ x' ≫ pullback.fst _ _ = w ≫ wi.α) ∧ (∀ (a : 𝓞 E) (e : wi.G ⟶ wi.G), e.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e.left ≫ ψ = ψ ≫ (f a).left) ∧ ∀ (K : Type) [Field K] (s : Sp K ⟶ Y.Z) (y : Sp K ⟶ Xo.XF c), s ≫ r = y ≫ C.i → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G s γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  first | exact @GlobalTheory.UPoinc.ActField.exists_action_field | exact GlobalTheory.UPoinc.ActField.exists_action_field | (intros; apply GlobalTheory.UPoinc.ActField.exists_action_field <;> assumption)
end
