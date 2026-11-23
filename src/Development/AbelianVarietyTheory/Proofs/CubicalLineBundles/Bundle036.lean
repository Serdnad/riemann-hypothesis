module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle008
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem polarised_of_grpObj (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) [GrpObj (schemeOver W)] (hc : IsCommMonObj (schemeOver W))
    (hη : η[schemeOver W].left = zero W) :
    IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
      (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
      Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
      Out.KTriv (schemeOver W) (originLB W) := by
  obtain ⟨hrig, hsym, hamp, hk⟩ := GlobalTheory.T.originLineBundle_polarisation R W hc hη
  exact ⟨isAbelianScheme_schemeOver R W hΔ hc, smoothOfRelativeDimension_toSpec_of_isUnit W hΔ,
    originLB_isLB W, hrig, hsym, hamp, hk⟩

theorem exists_grpObj_polarised (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) :
    ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ η[schemeOver W].left = zero W ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
        (hT : IsUnimodularSol (W.map ρ) T),
        (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
          Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
        ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
          y.left = ptHom W ρ Q hQ → (lift x y ≫ μ[schemeOver W]).left = ptHom W ρ T hT) ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P),
        ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
          ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN) ∧
      (IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
        (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
        Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
        Out.KTriv (schemeOver W) (originLB W)) ∧
      ∃ v : epsR R ⟶ schemeOver W,
        (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
          v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
        IsLieBasis ![v] := by
  obtain ⟨inst, hc, hη, hadd, hneg⟩ := GlobalTheory.T.exists_commGrpObj_weierstrassScheme R W hΔ
  exact ⟨inst, hc, hη, hadd, hneg, polarised_of_grpObj R W hΔ hc hη,
    GlobalTheory.WeierstrassLie.isLieBasis_eps R W hη⟩

theorem exists_polAV : ∀ (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R), IsUnit W.Δ →
    ∃ (P : Out.PolAV (Sp R)) (ψ : P.A.left ⟶ scheme W) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsIso ψ ∧
      ψ ≫ toSpec W = P.A.hom ∧ eSec P.A ≫ ψ = zero W ∧
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W hΔ
  obtain ⟨inst, hc, hη, -, -, ⟨hab, hsm, hlb, hrig, hsym, hamp, hk⟩, v, ⟨h, hv⟩, hbasis⟩ :=
    exists_grpObj_polarised R W hΔ
  let P : Out.PolAV (Sp R) :=
    { A := schemeOver W
      grp := inst
      isAb := hab
      g := 1
      smoothDim := hsm
      L := originLB W
      isLB := hlb
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hk }
  refine ⟨P, 𝟙 _, v, rfl, inferInstance, ?_, ?_, ⟨h, ?_⟩, hbasis⟩
  · rw [Category.id_comp]
    rfl
  · rw [Category.comp_id]
    exact hη
  · rw [Category.comp_id]
    exact hv

end GlobalTheory.WeierstrassCurve
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllComp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso (L.pull φ) L')
    (ψ : X'' ⟶ X') : LBIso (L.pull (ψ ≫ φ)) (L'.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) h

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem isPolFibre_comp {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {ψ : P''.A.left ⟶ P'.A.left}
    (h : IsPolFibre f P P' φ) (h' : IsPolFibre g P' P'' ψ) : IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap _ _) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem isVecOver_comp {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (h : IsVecOver f φ v v') (h' : IsVecOver g ψ v' v'') : IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  unfold IsVecOver at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc]
  exact congrArg (· ≫ v.left) (dualMapR_comp f g)

theorem exists_isPolFibre_lift {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {χ : P''.A.left ⟶ P.A.left}
    (h : IsPolFibre f P P' φ) (n : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ : P''.A.left ⟶ P'.A.left, ψ ≫ φ = χ ∧ IsPolFibre g P' P'' ψ := by
  have n' : IsGrpPullback P''.A P.A (spMap g ≫ spMap f) χ := n.2.1.congr (spMap_comp_spMap _ _).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n'.1.w.trans (Category.assoc _ _ _).symm
  have e : h.2.1.1.lift _ _ w ≫ φ = χ := h.2.1.1.lift_fst _ _ w
  refine ⟨h.2.1.1.lift _ _ w, e, n.1.trans h.1.symm,
    h.2.1.cancel (n'.congr rfl e.symm) (h.2.1.1.lift_snd _ _ w), ?_⟩
  refine LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 _).symm ?_
  rw [e]
  exact n.2.2

theorem isVecOver_cancel {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) (hψ : IsPullback ψ A''.hom A'.hom (spMap g))
    (h : IsVecOver f φ v v') (n : IsVecOver (g.comp f) (ψ ≫ φ) v v'') : IsVecOver g ψ v' v'' := by
  obtain ⟨w, hw, -⟩ := existsUnique_isVecOver hψ v'
  have hp : IsPullback (ψ ≫ φ) A''.hom A.hom (spMap (g.comp f)) := by
    rw [← spMap_comp_spMap]
    exact hψ.paste_horiz hφ
  rw [(existsUnique_isVecOver hp v).unique n (isVecOver_comp h hw)]
  exact hw

theorem isLieNormSq_iff {f : R →+* R'} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {φ : P'.A.left ⟶ P.A.left}
    {v : epsR R ⟶ P.A} {v' : epsR R' ⟶ P'.A} (h : IsPolFibre f P P' φ) (hv : IsVecOver f φ v v') (σ : R' →+* ℂ)
    (r : ℝ) : IsLieNormSq P' v' σ r ↔ IsLieNormSq P v (σ.comp f) r := by
  constructor
  · rintro ⟨Q, ψ, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    exact ⟨Q, ψ ≫ φ, w, u, Hm, χ, z, isPolFibre_comp h h₁, isVecOver_comp hv h₂, h₃⟩
  · rintro ⟨Q, ψ₀, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    obtain ⟨ψ, rfl, hψ⟩ := exists_isPolFibre_lift h h₁
    exact ⟨Q, ψ, w, u, Hm, χ, z, hψ, isVecOver_cancel h.2.1.1 hψ.2.1.1 hv h₂, h₃⟩

theorem ellMap_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → (∀ (R'' : Type) [CommRing R''] (ω'' : R'') (C'' : Ell H R'' ω'') (f' : R' →+* R'') (φ' : C''.P.A.left ⟶ C'.P.A.left), EllMap C'' C' f' φ' → EllMap C'' C (f'.comp f) (φ' ≫ φ)) ∧ (∀ σ : R' →+* ℂ, C.IsPrincipalAt (σ.comp f) → C'.IsPrincipalAt σ) ∧ ∀ (σ : R' →+* ℂ) (r : ℝ), Out.PolBaseChangeSt → (IsLieNormSq C'.P C'.v σ r ↔ IsLieNormSq C.P C.v (σ.comp f) r) := by
  intro E _ _ _ H R _ ω C R' _ ω' C' f φ h
  refine ⟨fun R'' _ ω'' C'' f' φ' h' => ⟨?_, isPolFibre_comp h.2.1 h'.2.1, isVecOver_comp h.2.2.1 h'.2.2.1, fun a => ?_⟩,
    fun σ hC Q ψ hψ => hC Q (ψ ≫ φ) (isPolFibre_comp h.2.1 hψ), fun σ r _ => isLieNormSq_iff h.2.1 h.2.2.1 σ r⟩
  · rw [RingHom.comp_apply, h.1, h'.1]
  · rw [← Category.assoc, h'.2.2.2 a, Category.assoc, h.2.2.2 a, Category.assoc]

end GlobalTheory.CM.EllComp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CMCount

theorem eq_top_of_countable {V L : Type} [AddCommGroup V] [Module ℂ V] [Countable L] (W : Submodule ℂ V) (P : L → V)
    (h : ∀ z, ∃ a, z - P a ∈ W) : W = ⊤ := by
  by_contra hW
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hW)
  choose a ha using h
  have : Function.Injective fun c : ℂ => a (c • v) := fun c d e => by
    by_contra hne
    have h1 := W.sub_mem (ha (c • v)) (ha (d • v))
    simp only at e
    rw [e, sub_sub_sub_cancel_right, ← sub_smul] at h1
    exact hv ((W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1)
  have : Countable ℂ := this.countable
  exact not_countable (Complex.ofReal_injective.countable)

theorem exists_basis {V L J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (b : Module.Basis J ℤ L) (P : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) : ∃ B : Module.Basis J ℝ V, ∀ i, B i = P (b i) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  refine ⟨(b.map (LinearEquiv.ofInjective P.toIntLinearMap hi)).ofZLatticeBasis ℝ Λ, fun i => ?_⟩
  rw [Module.Basis.ofZLatticeBasis_apply]
  rfl

theorem exists_real_equiv {V L : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (P P' : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range)
    (hs' : Submodule.span ℝ (Set.range P') = ⊤) : ∃ h : V ≃ₗ[ℝ] V, ∀ a, P' a = h (P a) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  have : Module.Free ℤ L := Module.Free.of_equiv (LinearEquiv.ofInjective P.toIntLinearMap hi).symm
  let b := Module.Free.chooseBasis ℤ L
  obtain ⟨B, hB⟩ := exists_basis b P hi hd hs
  obtain ⟨B', hB'⟩ := exists_basis b P' hi' hd' hs'
  refine ⟨B.equiv B' (Equiv.refl _), fun a => ?_⟩
  have : P'.toIntLinearMap = ((B.equiv B' (Equiv.refl _)).toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap :=
    b.ext fun i => by simp [← hB, ← hB']
  exact LinearMap.congr_fun this a

theorem exists_complex_equiv {U V I : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Module ℝ U] [Module ℝ V] [IsScalarTower ℝ ℂ U] [IsScalarTower ℝ ℂ V]
    (h : V ≃ₗ[ℝ] V) (F F' : I → (U →ₗ[ℂ] V)) (s : Set U) (hs : Submodule.span ℝ s = ⊤)
    (hF : ⨆ j, LinearMap.range (F j) = ⊤) (e : ∀ j, ∀ x ∈ s, F' j x = h (F j x)) :
    ∃ h' : V ≃ₗ[ℂ] V, ∀ v, h' v = h v := by
  have e' : ∀ j x, F' j x = h (F j x) := fun j x =>
    LinearMap.congr_fun (LinearMap.ext_on (f := (F' j).restrictScalars ℝ)
      (g := h.toLinearMap.comp ((F j).restrictScalars ℝ)) hs (e j)) x
  have hc : ∀ (c : ℂ) v, h (c • v) = c • h v := fun c v => by
    have hv : v ∈ ⨆ j, LinearMap.range (F j) := hF ▸ Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem j x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [← map_smul, ← e', ← e', map_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  exact ⟨{ h.toAddEquiv with map_smul' := hc }, fun _ => rfl⟩

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} {A B : Over S'} [GrpObj G] [GrpObj A] [GrpObj B] {f : S' ⟶ S}
    {α : A.left ⟶ G.left} {β : B.left ⟶ G.left} (hA : IsGrpPullback A G f α) (hB : IsGrpPullback B G f β) :
    ∃ κ : A ⟶ B, IsMonHom κ ∧ ∀ (T : Over S') (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z := by
  let κ : A ⟶ B := Over.homMk (hB.1.lift α A.hom hA.1.w) (hB.1.lift_snd ..)
  have hκ : κ.left ≫ β = α := hB.1.lift_fst ..
  refine ⟨κ, isMonHom_of_mul κ fun T x y => ?_, fun T z => ?_⟩
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    refine Over.OverMorphism.ext (hB.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [← hB.2 T (x ≫ κ) (y ≫ κ) x₀ y₀ (by simp [x₀, hκ]) (by simp [y₀, hκ]), hA.2 T x y x₀ y₀ rfl rfl,
      Over.comp_left, Category.assoc, hκ]
  · refine ⟨Over.homMk (hA.1.lift (z.left ≫ β) T.hom (by rw [Category.assoc, hB.1.w, Over.w_assoc]))
      (hA.1.lift_snd ..), Over.OverMorphism.ext (hB.1.hom_ext ?_ ?_)⟩
    · simp [hκ]
    · rw [Over.w, Over.w]

theorem exists_linear_onto {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B] {A₀ : Over (Sp ℂ)} [GrpObj A₀]
    (h₀ : IsAbelianScheme A₀) (hB : IsAbelianScheme B) {L₀ : LB A₀.left} {L : LB B.left} {g₀ g : ℕ}
    (u₀ : HolUnif A₀ L₀ g₀) (u : HolUnif B L g)
    (d₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (κ : A ⟶ B) [IsMonHom κ] (hκ : ∀ (T : Over (Sp ℂ)) (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z)
    {I : Type} (ψ : I → (A₀ ⟶ A)) (hψ : ∀ i, IsMonHom (ψ i)) (ho : OntoAt ψ (𝟙 (Sp ℂ))) :
    ∃ F : I → ((Fin g₀ → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ j, ∀ x ∈ u₀.Λ, F j x ∈ u.Λ) ∧
      ∀ z, ∃ w ∈ ⨆ j, LinearMap.range (F j), z - w ∈ u.Λ := by
  choose F hF hΛ _ using fun j => HomLinear.exists_linear_of_isMonHom A₀ B h₀ hB L₀ L g₀ g u₀ u d₁ d₂ (ψ j ≫ κ) (by have := hψ j; infer_instance)
  refine ⟨F, hΛ, fun z => ?_⟩
  have key : ∀ l : List (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ y ∈ l, ∃ w ∈ ⨆ j, LinearMap.range (F j), y ≫ κ = u.ex w) →
      ∃ w ∈ ⨆ j, LinearMap.range (F j), l.prod ≫ κ = u.ex w := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨0, Submodule.zero_mem _, by rw [(u.ker 0).2 u.Λ.zero_mem, List.prod_nil, MonObj.one_comp]⟩
    | cons y l ih =>
      intro h
      obtain ⟨w, hw, e⟩ := h y (by simp)
      obtain ⟨w', hw', e'⟩ := ih fun y hy => h y (by simp [hy])
      exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [List.prod_cons, MonObj.mul_comp, e, e', u.ex_add]⟩
  obtain ⟨y, hy⟩ := hκ _ (u.ex z)
  obtain ⟨n, i, x, e⟩ := ho y
  obtain ⟨w, hw, e'⟩ := key (List.ofFn fun m => x m ≫ ψ (i m)) fun y hy => by
    obtain ⟨m, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    obtain ⟨a, ha⟩ := u₀.ex_onto (x m)
    refine ⟨F (i m) a, Submodule.mem_iSup_of_mem (i m) ⟨a, rfl⟩, ?_⟩
    rw [hF, ha]
    exact Category.assoc ..
  refine ⟨w, hw, (u.ker _).1 ?_⟩
  have h1 : u.ex z = u.ex w := by rw [← hy, ← e', e]
  have h2 := u.ex_add (z - w) w
  rw [sub_add_cancel, h1] at h2
  exact mul_eq_right.1 h2.symm

end GlobalTheory.CMCount

namespace GlobalTheory

open CMCount

theorem countable_points_of_onto : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (P₀ : Out.PolAV (Sp ℂ)), Set.Countable {y : Sp ℂ ⟶ Xo.X | y ≫ Xo.s = spMap (algebraMap (KA l) ℂ) ∧ ∃ (t : SAB H (Sp ℂ)) (_ : SABMap t Xo.univ.t y) (n : ℕ) (ψ : Fin n → (P₀.A ⟶ t.G)), (∀ i, IsMonHom (ψ i)) ∧ OntoAt ψ (𝟙 (Sp ℂ))} := by
  intro hU hL E _ _ _ H D l Xo g ty FU P₀
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨u₀, -⟩ := hU P₀ rig hrig
  obtain ⟨s, hsΛ, hs, hli⟩ := exists_linearIndependent ℝ (u₀.Λ : Set (Fin P₀.g → ℂ))
  rw [u₀.full] at hs
  have : Finite s := hli.finite
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  have : ∀ i, Countable (FU.Di i).La := fun i =>
    have := (FU.Di i).fin
    Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
  let R : (Sp ℂ ⟶ Xo.X) → (Σ i : Fin FU.n, Σ n : ℕ, Fin n → s → (FU.Di i).La) → Prop := fun y c =>
    ∃ P, IsPeriod (FU.Di c.1) ty P ∧ FU.u c.1 P = y ∧ ∃ F : Fin c.2.1 → ((Fin P₀.g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      ⨆ j, LinearMap.range (F j) = ⊤ ∧ ∀ j (x : s), F j x = P (c.2.2 j x)
  have huniq : ∀ c, {y | R y c}.Subsingleton := by
    rintro ⟨i, n, c⟩ _ ⟨P, hP, rfl, F, hF, e⟩ _ ⟨P', hP', rfl, F', -, e'⟩
    obtain ⟨h, hh⟩ := exists_real_equiv P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
    obtain ⟨h', hh'⟩ := exists_complex_equiv h F F' s hs hF fun j x hx => by
      rw [e j ⟨x, hx⟩, e' j ⟨x, hx⟩, hh]
    exact (FU.fibre i P P' hP hP').2 ⟨LinearEquiv.refl _ _, h', fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, fun a => by rw [hh']; exact hh a⟩
  refine (Set.countable_iUnion fun c => (huniq c).countable).mono ?_
  rintro y ⟨hy, t, m, n, ψ, hψ, ho⟩
  obtain ⟨i, P, hP, rfl⟩ := FU.onto y hy
  obtain ⟨Q, φ, -, hQ, hQL, -⟩ := exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, -, -, Φ, -, d₁, d₂, -, -, hΦ, -⟩ := familyUnif_fibre_theta hU hL.weil E H D l Xo _ g ty FU i P hP Q φ hQ hQL
  obtain ⟨κ, hκ, hκ'⟩ := exists_compare m.cart hQ
  obtain ⟨F, hF, hF'⟩ := exists_linear_onto P₀.isAb Q.isAb u₀ u d₁ d₂ κ hκ' ψ hψ ho
  have hm : ∀ j (x : s), ∃ a, P a = Φ.symm (F j x) := fun j x =>
    (hΦ _).1 (by rw [Φ.apply_symm_apply]; exact hF j x (hsΛ x.2))
  choose c hc using hm
  refine Set.mem_iUnion.2 ⟨⟨i, n, c⟩, P, hP, rfl, fun j => Φ.symm.toLinearMap ∘ₗ F j, ?_, fun j x => (hc j x).symm⟩
  refine eq_top_of_countable _ P fun z => ?_
  obtain ⟨w, hw, hz⟩ := hF' (Φ z)
  obtain ⟨a, ha⟩ := (hΦ (z - Φ.symm w)).1 (by rwa [map_sub, Φ.apply_symm_apply])
  refine ⟨a, ?_⟩
  rw [ha, sub_sub_cancel]
  simp only [LinearMap.range_comp, ← Submodule.map_iSup]
  exact Submodule.mem_map_of_mem hw

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem isTen_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (t : IsTen C D h T) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), EllMap C' C f φ → ∃ t' : IsTen C' D h T', ∀ a, (t'.ten.tmul a).left ≫ m.φ = φ ≫ (t.ten.tmul a).left := by
  intro E _ _ _ H R _ ω C D h T t R' _ ω' C' f φ T' m hC
  obtain ⟨-, ⟨-, hφ, iC⟩, -, hact⟩ := hC
  have hφ' : Serre.IsLinearPullback C'.act C.act (spMap f) φ := ⟨hφ, hact⟩
  have hψ : Serre.IsLinearPullback (Serre.comapAct T'.t.act (algebraMap (OK H) (𝓞 E)))
      (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (spMap f) m.φ := ⟨m.cart, fun c => m.act _⟩
  have iT : LBIso (T.t.PP.L.pull m.φ) T'.t.PP.L :=
    LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1)
  have e := fun a => t.ten.baseChange_tmul hφ' hψ a
  refine ⟨⟨t.ten.baseChange hφ' hψ, fun s a => ?_, fun a b => ?_⟩, e⟩
  · refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine (e (s • a)).trans ?_
    rw [t.lin, Over.comp_left, Over.comp_left, Category.assoc, m.act s, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (T.t.act.act s).left) (e a).symm
  · exact lamEq_baseChange _ _ (spMap f) C.P.A C.P.A T.t.G C.P.A C'.P.A C'.P.A T'.t.G C'.P.A φ φ m.φ φ
      hφ.1.w hφ.1.w m.cart hφ T.t.PP.L C.P.L T'.t.PP.L C'.P.L T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB iT iC
      _ _ _ _ _ _ _ _ (e a) (e b) (hact _) ((Category.id_comp _).trans (Category.comp_id _).symm) (t.lam a b)

end GlobalTheory.CM

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Factor

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    Chart.dualMapR (f'.comp f) = (Chart.dualMapR f').comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem ellMap_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' R'' : Type} [CommRing R]
    [CommRing R'] [CommRing R''] {f : R →+* R'} {f' : R' →+* R''} {ω : R} {ω' : R'} {ω'' : R''} {C : Ell H R ω}
    {C' : Ell H R' ω'} {C'' : Ell H R'' ω''} {φ : C'.P.A.left ⟶ C.P.A.left} {ψ : C''.P.A.left ⟶ C.P.A.left}
    (h : EllMap C' C f φ) (k : EllMap C'' C (f'.comp f) ψ) :
    ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ := by
  obtain ⟨hω, ⟨hg, hp, hL⟩, hv, ha⟩ := h
  obtain ⟨kω, ⟨kg, kp, kL⟩, kv, ka⟩ := k
  rw [← spMap_comp_spMap] at kp
  have w : ψ ≫ C.P.A.hom = (C''.P.A.hom ≫ spMap f') ≫ spMap f := by rw [kp.1.w, Category.assoc]
  obtain ⟨l, h₁, h₂⟩ : ∃ l : C''.P.A.left ⟶ C'.P.A.left, l ≫ φ = ψ ∧ l ≫ C'.P.A.hom = C''.P.A.hom ≫ spMap f' :=
    ⟨hp.1.lift _ _ w, hp.1.lift_fst _ _ w, hp.1.lift_snd _ _ w⟩
  subst h₁
  refine ⟨l, ⟨hω ▸ kω, ⟨kg.trans hg.symm, hp.cancel kp h₂, ?_⟩, ?_, fun a => ?_⟩, rfl⟩
  · have e : LBIso (C.P.L.pull (l ≫ φ)) (C'.P.L.pull l) :=
      LBIso.chartPull (chartPullSame C.P.L _ _ _ l fun _ => rfl) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull C'.P.L l l rfl) hL
    exact LBIso.trans (pull_isLB C'.P.isLB _) (pull_isLB C.P.isLB _) C''.P.isLB e.symm kL
  · unfold IsVecOver at hv kv ⊢
    apply hp.1.hom_ext
    · rw [Category.assoc, kv, Category.assoc, hv, dualMapR_comp, ← spMap_comp_spMap, Category.assoc]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w C''.v, Category.assoc, Over.w C'.v]
      refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
      congr 1
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · apply hp.1.hom_ext
    · rw [Category.assoc, ka, Category.assoc, Category.assoc, ha]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w, Category.assoc, Over.w, h₂]

theorem ellMap_cancel_and_sabMap_cancel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R''),
  (∀ (ω : R) (ω' : R') (ω'' : R'') (C : Ell H R ω) (C' : Ell H R' ω') (C'' : Ell H R'' ω'') (φ : C'.P.A.left ⟶ C.P.A.left) (ψ : C''.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → EllMap C'' C (f'.comp f) ψ → ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ) ∧
  ∀ (S : Scheme.{0}) (y : Sp R' ⟶ S) (y' : Sp R'' ⟶ S) (t : SAB H S) (t' : SAB H (Sp R')) (t'' : SAB H (Sp R'')) (m : SABMap t' t y) (n : SABMap t'' t y'), spMap f' ≫ y = y' → ∃ m' : SABMap t'' t' (spMap f'), m'.φ ≫ m.φ = n.φ := by
  intro E _ _ _ H R R' R'' _ _ _ f f'
  refine ⟨fun _ _ _ _ _ _ _ _ h k => ellMap_cancel h k, fun S y y' t t' t'' m n e => ?_⟩
  subst e
  obtain ⟨m', h⟩ := ObjMaps.exists_sab_cancel m n
  exact ⟨m', h.symm⟩

end GlobalTheory.CM.Factor
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem homExtDvr_of_card_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → HomExtDvr := by
  intro h
  exact homExtDvr_iff.2 (GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion h))

end GlobalTheory.CM
end
