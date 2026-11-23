module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import GroundTheory.GlobalFields.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SumAffine

theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A T : C) [GrpObj A]
    (b : T ⟶ A) : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)) := by
  refine ⟨lift (fst A T * (snd A T ≫ b⁻¹)) (snd A T), ?_, ?_⟩
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp

theorem isAffineOpen_preimage_translate (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R)) [IsAffine T.left] (b : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ b)).left ⁻¹ᵁ V) := by
  haveI : IsAffine (Sp R) := by unfold Sp; infer_instance
  haveI : IsAffineHom T.hom := inferInstance
  haveI : IsAffineHom (fst A T).left := by
    change IsAffineHom (pullback.fst A.hom T.hom)
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback A.hom T.hom).flip inferInstance
  haveI := isIso_shear A T b
  have h : fst A T * (snd A T ≫ b) = lift (fst A T * (snd A T ≫ b)) (snd A T) ≫ fst A T := by simp
  haveI : IsAffineHom (fst A T * (snd A T ≫ b)).left := by
    rw [h, Over.comp_left]
    haveI : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)).left :=
      inferInstanceAs (IsIso ((Over.forget (Sp R)).map (lift (fst A T * (snd A T ≫ b)) (snd A T))))
    infer_instance
  exact hV.preimage _

theorem isAffineOpen_preimage_add_inf_preimage_sub (R : Type) [CommRing R] (A : Over (Sp R))
    [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R))
    [IsAffine T.left] (a : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓
      (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  have h1 := isAffineOpen_preimage_translate R A V hV T a
  have h2 := isAffineOpen_preimage_translate R A V hV T a⁻¹
  rw [GrpObj.comp_inv] at h2
  haveI : IsSeparated (snd A T).left := by
    change IsSeparated (pullback.snd A.hom T.hom)
    infer_instance
  haveI : (A ⊗ T).left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (snd A T).left]
    infer_instance
  exact h1.inf h2

end GlobalTheory.SumAffine
end

section

open IsDedekindDomain IsLocalRing

namespace GlobalTheory.IntAdicHensel

theorem henselianLocalRing_and_finite_residueField :
    ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧
      Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  intro v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers ℚ)
  haveI : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers ℚ)
    (maximalIdeal (v.adicCompletionIntegers ℚ))
  refine ⟨GlobalTheory.henselianLocalRing_of_henselianRing _, ?_⟩
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv

end GlobalTheory.IntAdicHensel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.SymCube

open GlobalTheory.UU

theorem sym_cube (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  let G := D.P.A
  let a := x3 G 0
  let b := x3 G 1
  let sy := fun p : G3 G ⟶ G => LB.pullGen D.P.L _ _ D.sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen D.P.L (thφ G (x3 G)) thε D.cub.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ D.sym_gen _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ D.cub.isGen _
  have vs : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J → ∀ p,
      val (sy p) σ.left z J = val D.sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen D.P.L _ _ _ _ (sy (a * b)) (cu b b⁻¹ a⁻¹)
  let t₂ := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (sy a) (sy b)) (cu a a⁻¹ b)
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J →
      val t₁ σ.left z J = val D.sym ((σ ≫ a) * (σ ≫ b)).left z J * cubV D.cub z J (σ ≫ b) (σ ≫ b)⁻¹ (σ ≫ a)⁻¹ ∧
      val t₂ σ.left z J = val D.sym (σ ≫ a).left z J * val D.sym (σ ≫ b).left z J *
        cubV D.cub z J (σ ≫ a) (σ ≫ a)⁻¹ (σ ≫ b) := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs σ hJ _) (val_cub D.cub σ hJ _ _ _))
    · rw [← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs σ hJ _) (vs σ hJ _))) (val_cub D.cub σ hJ _ _ _))
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  let ρ : T ⟶ G3 G := lift x (lift y 1)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have h3 := GlobalTheory.UU.surjective_cube GlobalTheory.globalFns_holds D.P.isAb
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' D.P.isLB (fun V _ k => ?_) (G3 G).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gc _ _ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gs _)) (gc _ _ _))
      (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym a k) (prod_sym b k))
        (prod_cub a a⁻¹ b k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _ (prod_sym (a * b) k) (prod_cub b b⁻¹ a⁻¹ k)).symm)
      have m₁ : b * b⁻¹ * a⁻¹ = a⁻¹ := by rw [mul_inv_cancel, _root_.one_mul]
      have m₂ : b * b⁻¹ = 1 := mul_inv_cancel b
      have m₃ : b * a⁻¹ = a⁻¹ * b := mul_comm _ _
      have m₄ : b⁻¹ * a⁻¹ = (a * b)⁻¹ := (mul_inv_rev a b).symm
      have m₅ : a * a⁻¹ * b = b := by rw [mul_inv_cancel, _root_.one_mul]
      have m₆ : a * a⁻¹ = 1 := mul_inv_cancel a
      rw [m₁, m₂, m₃, m₄, m₅, m₆]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val D.sym (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI D.sym (eSec G) _).symm.trans ((val_corr hI D.sym_rig _).trans (val_one _))
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁]
      simp only [inv_one, _root_.mul_one, s1, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁] at this

end GlobalTheory.PolDeg.SymCube
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.ChartSmooth

theorem isStandardSmooth_C (k : Type) [CommRing k] (D : ℕ) :
    (algebraMap k (MvPolynomial (Fin D) k)).IsStandardSmoothOfRelativeDimension D := by
  let P₀ : Algebra.Presentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := Algebra.Generators.mvPolynomial k (Fin D)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2
    (P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension]))

theorem isStandardSmooth_algX {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (x : Fin D → Γ(X, U)) (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (algX p U).IsStandardSmoothOfRelativeDimension D := by
  have hC : (MvPolynomial.eval₂Hom (algX p U) x).comp (algebraMap k _) = algX p U :=
    RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  have h := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 hx).comp
    (isStandardSmooth_C k D)
  rwa [hC, zero_add] at h

theorem smooth_of_etale {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (hU : IsAffineOpen U) (x : Fin D → Γ(X, U))
    (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    SmoothOfRelativeDimension D (U.ι ≫ p) := by
  have hA : IsAffine U.toScheme := hU
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv (isStandardSmooth_algX p x hx)
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    U.topIso.symm.commRingCatIsoToRingEquiv h₁
  refine (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension D)).2
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_)
  have e : (U.ι ≫ p).appTop = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (by simp) ≫ U.topIso.inv := by
    rw [Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Opens.topIso_inv,
      Scheme.Opens.ι_app, Category.assoc]
    exact (congrArg (p.app ⊤ ≫ ·) (Eq.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))
      (X.presheaf.map_comp _ _))).trans (Category.assoc _ _ _).symm
  rw [e]
  exact h₂

end GlobalTheory.ChartSmooth
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSemiOpen

theorem isAb_pullback_open {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsSemiAbelian A) (U : S.Opens)
    (hU : IsProper (A.hom ∣_ U)) : IsAbelianScheme ((Over.pullback U.ι).obj A) := by
  have hB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback U.ι A hA
  refine ⟨hB.comm, hB.smooth, ?_, hB.geomConnected⟩
  change IsProper (pullback.snd A.hom U.ι)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

end GlobalTheory.SquareSemiOpen
end
