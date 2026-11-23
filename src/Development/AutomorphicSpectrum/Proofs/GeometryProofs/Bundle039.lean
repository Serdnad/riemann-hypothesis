module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PeriodCoord

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {A R : Type} [CommRing A] [CommRing R]

theorem dualMap_comp_base (i : Sp A ⟶ X) (θ : A →+* R) :
    spMap (dualMap θ) ≫ (epsAt i).hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
  have e : (CommRingCat.ofHom (algebraMap A (DualNumber A))) ≫ CommRingCat.ofHom (dualMap θ) =
      CommRingCat.ofHom θ ≫ CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show dualMap θ (algebraMap A (DualNumber A) a) = algebraMap R (DualNumber R) (θ a)
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [dualMap]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show spMap (dualMap θ) ≫ Spec.map _ ≫ i = Spec.map _ ≫ 𝟙 (Sp R) ≫ spMap θ ≫ i
  rw [Category.id_comp, ← Category.assoc, e', Category.assoc]

def pushEps (i : Sp A ⟶ X) (θ : A →+* R) (v : epsAt i ⟶ G) : epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ G :=
  Over.homMk (spMap (dualMap θ) ≫ v.left) (by
    have e : (spMap (dualMap θ) ≫ v.left) ≫ G.hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
      rw [Category.assoc, Over.w v, dualMap_comp_base]
    exact e)

theorem isTanAt_pushEps (i : Sp A ⟶ X) (θ : A →+* R) {v : epsAt i ⟶ G} (h : IsTanAt G i v) :
    IsTanAt G (𝟙 (Sp R) ≫ spMap θ ≫ i) (pushEps i θ v) := by
  unfold IsTanAt at h ⊢
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap θ)) =
      Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp [dualMap]
  let s : Over.mk (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ Over.mk i :=
    Over.homMk (spMap θ) (by simp)
  have h1 : s ≫ (1 : Over.mk i ⟶ G) = 1 := MonObj.comp_one s
  have h2 := congrArg CommaMorphism.left h1
  refine Eq.trans ?_ h2
  change _ = spMap θ ≫ (1 : Over.mk i ⟶ G).left
  rw [← h]
  change Spec.map _ ≫ spMap (dualMap θ) ≫ v.left = _
  rw [← Category.assoc, key, Category.assoc]

theorem exists_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  intro E _ _ _ H X t A _ i N v R _ t' θ m g M hv
  have hx : ∀ k, ∃ e : Fin g → R, (M.pt e).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := fun k => by
    have ht : IsTanAt t'.G (𝟙 (Sp R)) ((LiePull.tanPts m.cart (𝟙 (Sp R))).symm (pushEps i θ (v k))) :=
      (LiePull.isTan_iff m.cart (𝟙 (Sp R)) _).1 (by
        rw [MulEquiv.apply_symm_apply]
        exact isTanAt_pushEps i θ (hv k))
    obtain ⟨e, he⟩ := M.onto _ ht
    refine ⟨e, ?_⟩
    rw [he, ← LiePull.pts_left m.cart (LiePull.eps_assoc (𝟙 (Sp R))), MulEquiv.apply_symm_apply]
    rfl
  choose x hx using hx
  exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.Ar.PeriodCoord
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart

theorem exists_eq_div_adjoin (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) (a : Ω) :
    ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  obtain ⟨U, hU, hUc⟩ := hT.affine c hc
  have hreg0 : ∀ b : Ω, b ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
    intro b
    obtain ⟨s, hs⟩ := hT.gen.bij.2 b
    show b ∈ (genMap ξ _).range
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    first
      | exact hs
      | (rw [Category.id_comp]; exact hs)
      | simpa using hs
  have hgU : genPt ξ ∈ U :=
    (hUc (genPt ξ)).mpr ⟨specializes_refl _, And.intro hc fun _ => hreg0 _⟩
  let φ : Γ(X, U) →+* Ω := (X.presheaf.germ U (genPt ξ) hgU ≫ Scheme.stalkClosedPointTo ξ).hom
  have key : ∀ r : Γ(X, U), φ r ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (hT.ring c hc (φ r)).mpr fun p hp => ?_
    have hpU : p.1 ∈ U := (hUc p.1).mpr ⟨p.2, hp⟩
    show φ r ∈ (genMap ξ p).range
    refine RingHom.mem_range.mpr ⟨(X.presheaf.germ U p.1 hpU).hom r, ?_⟩
    have e0 : X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 =
        X.presheaf.germ U (genPt ξ) hgU := by
      first
        | simp
        | exact TopCat.Presheaf.germ_stalkSpecializes X.presheaf hpU p.2
        | exact TopCat.Presheaf.germ_stalkSpecializes hpU p.2
    show (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom
        ((X.presheaf.germ U p.1 hpU).hom r) = φ r
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
    first
      | exact congrArg (fun (m : Γ(X, U) ⟶ CommRingCat.of Ω) => CommRingCat.Hom.hom m r)
          ((reassoc_of% e0) (Scheme.stalkClosedPointTo ξ))
      | (simp only [reassoc_of% e0]; rfl)
  have gres : ∀ {W W' : X.Opens} (hle : W ≤ W') (hw : genPt ξ ∈ W) (z : Γ(X, W')),
      (X.presheaf.germ W (genPt ξ) hw).hom ((X.presheaf.map (homOfLE hle).op).hom z) =
        (X.presheaf.germ W' (genPt ξ) (hle hw)).hom z := by
    intro W W' hle hw z
    have e : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ W (genPt ξ) hw =
        X.presheaf.germ W' (genPt ξ) (hle hw) := by
      first
        | simp
        | exact TopCat.Presheaf.germ_res _ _ _ _
    exact congrArg (fun m => m.hom z) e
  obtain ⟨s0, hs0⟩ : ∃ s0 : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s0 = a :=
    hT.gen.bij.2 a
  obtain ⟨V, hV, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s0
  obtain ⟨t, htV, hgt⟩ := hU.exists_basicOpen_le ⟨genPt ξ, hV⟩ hgU
  have hD : genPt ξ ∈ X.basicOpen t := hgt
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X U hU t
    ((X.presheaf.map (homOfLE htV).op).hom f)
  have hy' : (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom y =
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom t) ^ n *
        (X.presheaf.map (homOfLE htV).op).hom f := hy
  have h2 : (X.presheaf.germ U (genPt ξ) hgU).hom y =
      ((X.presheaf.germ U (genPt ξ) hgU).hom t) ^ n * (X.presheaf.germ V (genPt ξ) hV).hom f := by
    have h2' := congrArg (X.presheaf.germ (X.basicOpen t) (genPt ξ) hD).hom hy'
    simp only [map_mul, map_pow, gres] at h2'
    exact h2'
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have hφ : ∀ r, φ r = ψ ((X.presheaf.germ U (genPt ξ) hgU).hom r) := by
    intro r
    first
      | rfl
      | simp [φ, ψ]
  have hs0' : ψ ((X.presheaf.germ V (genPt ξ) hV).hom f) = a := hs0
  have h3 : φ y = φ t ^ n * a := by
    rw [hφ, hφ, h2, map_mul, map_pow, hs0']
  have hunit : IsUnit ((X.presheaf.germ U (genPt ξ) hgU).hom t) :=
    (X.mem_basicOpen t (genPt ξ) hgU).mp hD
  have hφt : φ t ≠ 0 := by
    rw [hφ]
    exact (hunit.map ψ).ne_zero
  refine ⟨φ y, key y, φ (t ^ n), key (t ^ n), ?_, ?_⟩
  · rw [map_pow]
    exact pow_ne_zero _ hφt
  · rw [map_pow]
    exact eq_div_of_mul_eq (pow_ne_zero _ hφt) (by rw [h3]; ring)

end GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.ValLift

theorem valAt_of_stalkMap_surjective : ∀ (X₀ X' : Scheme.{0}) (Ω R : Type) [Field Ω] [CommRing R] [IsLocalRing R]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R), ξ' ≫ π = ξ →
    Function.Surjective (π.stalkMap (centre z)).hom → ValAt ξ' z a r → ValAt ξ (z ≫ π) a r := by
  intro X₀ X' Ω R _ _ _ ξ ξ' π z a r hξ hsurj hv
  subst hξ
  obtain ⟨h', s', hs'a, hs'r⟩ := hv
  obtain ⟨s, hs⟩ := hsurj s'
  have hsp : genPt (ξ' ≫ π) ⤳ centre (z ≫ π) := h'.map π.continuous
  refine ⟨hsp, s, ?_, ?_⟩
  · rw [← hs'a, ← hs]
    have key : X₀.presheaf.stalkSpecializes hsp ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π) =
        π.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h' ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo ξ' := by
      rw [AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
      exact AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap_assoc π (genPt ξ') (centre z) h'
        (AlgebraicGeometry.Scheme.stalkClosedPointTo ξ')
    show (CommRingCat.Hom.hom (X₀.presheaf.stalkSpecializes hsp ≫
      AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π))) s = _
    rw [key]
    rfl
  · rw [← hs'r, ← hs, AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.ValLift
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isHT_mul_add : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') :=
  @PositivityTheory.HtPt.Htat.ht_add

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.HT

private lemma valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt y U h (a - b) = valAt y U h a - valAt y U h b := by
  simp [valAt, map_sub]

private lemma exists_dual_of_dvd {R : Type} [CommRing R] [IsDomain R] {L : Type} [AddCommGroup L]
    [Module R L] (c : R) (hc : c ≠ 0) (d : Module.Dual R L) (h : ∀ e, c ∣ d e) :
    ∃ u : Module.Dual R L, d = c • u := by
  choose f hf using h
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply mul_left_cancel₀ hc
    rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)]
  · intro r x
    apply mul_left_cancel₀ hc
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hf, map_smul, smul_eq_mul, hf x]
    ring
  · ext e
    show d e = c • f e
    rw [hf e, smul_eq_mul]

theorem isHT_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → (N : R) ≠ 0 → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → (Γ.IsHT i M N χ w' ↔ ∃ u : Module.Dual R L, w' = w + N • u) := by
  intro R _ _ T _ _ Γ S G _ _ x N i hT hsm hN L _ _ M χ w w' hw
  obtain ⟨s, hs, hsv⟩ := hw
  constructor
  · rintro ⟨s', hs', hsv'⟩
    have hss : s' = s := by
      have h0 := GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ (s' - s) (fun t h => by
        rw [valAt_sub', hs' t, hs t, sub_self])
      exact sub_eq_zero.mp h0
    subst hss
    have hdvd : ∀ e, (N : R) ∣ w' e - w e := by
      intro e
      obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
      obtain ⟨v', hv1', hv2', hv3'⟩ := hsv' e
      have hvv : v' = v := (GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i hT L M e).unique ⟨hv1', hv2'⟩ ⟨hv1, hv2⟩
      subst hvv
      rw [hv3] at hv3'
      have h1 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) := by
        simpa using congrArg TrivSqZeroExt.snd hv3'
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact h1.symm
    obtain ⟨u, hu⟩ := exists_dual_of_dvd (N : R) hN (w' - w) (fun e => by simpa using hdvd e)
    refine ⟨u, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul R, ← hu]
    abel
  · rintro ⟨u, rfl⟩
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
    refine ⟨v, hv1, hv2, ?_⟩
    have h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((N • u) e) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, ← Nat.cast_smul_eq_nsmul R,
        LinearMap.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    rw [hv3, LinearMap.add_apply, map_add (f := _), h0, add_zero]

end GlobalTheory.CompanionTheory.Ar.BT.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SectionNear

theorem germ_closedPoint {Y : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem fromSpec_appLE_self {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V) :
    hV.fromSpec.appLE V ⊤ h ≫ (Scheme.ΓSpecIso Γ(T, V)).hom = 𝟙 _ := by
  have e : (Spec Γ(T, V)).presheaf.map (eqToHom hV.fromSpec_preimage_self).op ≫
      (Spec Γ(T, V)).presheaf.map (homOfLE h).op = 𝟙 _ := by
    have e₀ : (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [← Functor.map_comp, e₀, CategoryTheory.Functor.map_id]
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    reassoc_of% e]
  simp

theorem spMap_fromSpec_appLE {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (χ : Γ(T, V) →+* ℂ)
    (h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = CommRingCat.ofHom χ := by
  have h₁ : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have n := Scheme.ΓSpecIso_naturality (R := Γ(T, V)) (S := CommRingCat.of ℂ) (CommRingCat.ofHom χ)
  have a : (spMap χ).appLE ⊤ ⊤ le_top = Scheme.Hom.appTop (spMap χ) := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h₁ le_top, a, Category.assoc, n,
    reassoc_of% (fromSpec_appLE_self hV h₁)]

theorem section_near : ∀ (X T : Scheme.{0}) (j : T ⟶ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (y₀ : Sp ℂ ⟶ T) (t : Ω) (r₀ : ℂ), ValAt ξ (y₀ ≫ j) t r₀ → ∃ W₁ : T.Opens, ⊤ ≤ y₀ ⁻¹ᵁ W₁ ∧ ∀ (V : T.Opens) (hV : IsAffineOpen V), V ≤ W₁ → ∃ g : Γ(T, V), ∀ (χ : Γ(T, V) →+* ℂ) (r : ℂ), ValAt ξ ((spMap χ ≫ hV.fromSpec) ≫ j) t r → r = χ g := by
  intro X T j Ω _ ξ hξ y₀ t r₀ h₀
  obtain ⟨h, s, hs, -⟩ := h₀
  obtain ⟨N, hp, G, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s
  have hgen : genPt ξ ∈ N := h.mem_open N.2 hp
  have hgerm : ∀ (p : Cpt ξ) (hp : p.1 ∈ N), genMap ξ p (X.presheaf.germ N p.1 hp G) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ N (genPt ξ) hgen G) := by
    intro p hp
    have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
    have e' : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ N p.1 hp G) =
        X.presheaf.germ N (genPt ξ) hgen G := by
      rw [← e]; rfl
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom e'
  refine ⟨j ⁻¹ᵁ N, ?_, fun V hV hVN => ⟨j.appLE N V hVN G, fun χ r hr => ?_⟩⟩
  · intro x _
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst hx
    exact hp
  · obtain ⟨h', s', hs', rfl⟩ := hr
    have hcV : (spMap χ ≫ hV.fromSpec) (IsLocalRing.closedPoint ℂ) ∈ V := by
      have : hV.fromSpec ((spMap χ) (IsLocalRing.closedPoint ℂ)) ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
      rw [hV.range_fromSpec] at this
      exact this
    have hq : centre ((spMap χ ≫ hV.fromSpec) ≫ j) ∈ N := hVN hcV
    have e : s' = X.presheaf.germ N _ hq G :=
      hξ.inj ⟨_, h'⟩ (hs'.trans ((hs.symm.trans (hgerm ⟨_, h⟩ hp)).trans (hgerm ⟨_, h'⟩ hq).symm))
    subst e
    have e₂ : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hcV).ge
    have k := germ_closedPoint (R := CommRingCat.of ℂ) ((spMap χ ≫ hV.fromSpec) ≫ j) N hq
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge
    have d : ((spMap χ ≫ hV.fromSpec) ≫ j).appLE N ⊤
        (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = j.appLE N V hVN ≫ CommRingCat.ofHom χ := by
      rw [← Scheme.Hom.appLE_comp_appLE (spMap χ ≫ hV.fromSpec) j N V ⊤ hVN e₂, Category.assoc,
        spMap_fromSpec_appLE hV χ e₂]
    exact congrArg (fun φ => φ.hom G) (k.trans d)

end GlobalTheory.CompanionTheory.Ar.SectionNear
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ValEmb

theorem valAt_pull {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}
    (j : X ⟶ Spec (CommRingCat.of A)) (x : Spec (CommRingCat.of B) ⟶ X) (ρ : A →+* B)
    (h : x ≫ j = Spec.map (CommRingCat.ofHom ρ)) (f : A) :
    valAt x ⊤ le_top (j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)) = ρ f := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop ≫ x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      = CommRingCat.ofHom ρ := by
    have : j.appTop ≫ x.appTop = (Spec.map (CommRingCat.ofHom ρ)).appTop := by
      rw [← h, Scheme.Hom.comp_appTop]
    rw [reassoc_of% this, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have h2 := congrArg (fun φ => φ.hom f) h1
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]
  simpa using h2

theorem valAt_sub {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem val_emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  intro R _ _ T _ _ Γ j hj f s hs B _ y ρ hy
  have hz : s - j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f) = 0 := by
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ _ fun t h => ?_
    rw [valAt_sub, hs t, valAt_pull j (Γ.pt t).left _ (hj.pt t) f]
    simp
  rw [sub_eq_zero.mp hz]
  exact valAt_pull j y ρ hy f

end GlobalTheory.CompanionTheory.Ar.BT.ValEmb
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.coords_generate_function_field : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (W : Scheme.{0}) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω), CoordTie F ξ' t → ∃ c₀, t c₀ ≠ 0 ∧ ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), ∃ h ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac | exact GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.coords_single_block_segre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω), CoordTie ℤ ξ x → CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k => ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | exact GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_pullback_action : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V') (O : Type) [CommRing O] (act : O → (G ⟶ G)) (act' : O → (G' ⟶ G')) (ρ : O →+* Module.End Ω V) (ρ' : O →+* Module.End Ω' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → M.IsActOf act ρ → M'.IsActOf act' ρ' → (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) → ∀ a e, ρ' a (j e) = j (ρ a e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBaseAct.baseChange_act | exact GlobalTheory.CompanionTheory.Ar.LieBaseAct.baseChange_act | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBaseAct.baseChange_act <;> assumption)
end
