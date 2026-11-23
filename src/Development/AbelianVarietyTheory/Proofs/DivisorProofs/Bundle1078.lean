module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle990
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle480
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AddFamLift

theorem isPullback_lift {S : Scheme.{0}} (Z U S' : Over S) {W : Scheme.{0}} {pr : W ⟶ Z.left} {t : W ⟶ U.left}
    (hp : IsPullback pr t Z.hom U.hom) (j : (Z ⊗ (U ⊗ S')).left ⟶ W)
    (hj₁ : j ≫ pr = (fst Z (U ⊗ S')).left) (hj₂ : j ≫ t = (snd Z (U ⊗ S')).left ≫ (fst U S').left) :
    IsPullback j ((snd Z (U ⊗ S')).left ≫ (snd U S').left) (t ≫ U.hom) S'.hom := by
  have outer : IsPullback (fst Z (U ⊗ S')).left (snd Z (U ⊗ S')).left Z.hom (U ⊗ S').hom :=
    IsPullback.of_hasPullback Z.hom (U ⊗ S').hom
  have e : (U ⊗ S').hom = (fst U S').left ≫ U.hom := (Over.w _).symm
  rw [e, ← hj₁] at outer
  have left : IsPullback j (snd Z (U ⊗ S')).left t (fst U S').left := IsPullback.of_right outer hj₂ hp
  exact left.paste_vert (IsPullback.of_hasPullback U.hom S'.hom)

abbrev Ov {R C : Type} [CommRing R] [CommRing C] (σ : R →+* C) : Over (Sp R) := Over.mk (spMap σ)

theorem finiteRing_sq_sub_mul_sq_eq_of_card (hAb : AbLift) (R : Type) [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥) (A : Over (Sp R)) [GrpObj A]
    (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (C : Type) [CommRing C] (σ : R →+* C)
    (N : LB (A ⊗ (Ov σ ⊗ Ov (Ideal.Quotient.mk J))).left) (hN : N.IsLB) (hadd : IsAdditive N) :
    ∃ c : Pic (A ⊗ Ov σ).left, CechPic.pull (A ◁ fst (Ov σ) (Ov (Ideal.Quotient.mk J))).left c = cls N hN := by
  letI := σ.toAlgebra
  let U := Ov σ
  let S' := Ov (Ideal.Quotient.mk J)
  obtain ⟨B, _, pr, pr', hB, hBg, hp, hp', hμ, h₁, h₂, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R C A g hA hg
  have hp : IsPullback pr B.hom A.hom U.hom := hp
  have hp' : IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom U.hom := hp'
  have wZ : ∀ Z : Over (Sp R), (fst Z (U ⊗ S')).left ≫ Z.hom = ((snd Z (U ⊗ S')).left ≫ (fst U S').left) ≫ U.hom :=
    fun Z ↦ by rw [Category.assoc, Over.w, Over.w, Over.w]
  obtain ⟨i, hi₁, hi₂⟩ : ∃ i : (A ⊗ (U ⊗ S')).left ⟶ B.left, i ≫ pr = (fst A (U ⊗ S')).left ∧
      i ≫ B.hom = (snd A (U ⊗ S')).left ≫ (fst U S').left :=
    ⟨hp.lift _ _ (wZ A), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  obtain ⟨i', hi'₁, hi'₂⟩ : ∃ i' : ((A ⊗ A) ⊗ (U ⊗ S')).left ⟶ (B ⊗ B).left,
      i' ≫ pr' = (fst (A ⊗ A) (U ⊗ S')).left ∧ i' ≫ (B ⊗ B).hom = (snd (A ⊗ A) (U ⊗ S')).left ≫ (fst U S').left :=
    ⟨hp'.lift _ _ (wZ (A ⊗ A)), hp'.lift_fst _ _ _, hp'.lift_snd _ _ _⟩
  have hJ' : J.map σ ^ 2 = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have th : IsThick (J.map σ) B.hom i := by
    have q := isPullback_lift A U S' hp i hi₁ hi₂
    exact GlobalTheory.T.isIdealThickeningImmersion_of_isPullback_square_zero_quotient R C σ J hJ _ _ B.hom _ i q
  have th' : IsThick (J.map σ) (B ⊗ B).hom i' := by
    have q := isPullback_lift (A ⊗ A) U S' hp' i' hi'₁ hi'₂
    exact GlobalTheory.T.isIdealThickeningImmersion_of_isPullback_square_zero_quotient R C σ J hJ _ _ (B ⊗ B).hom _ i' q
  have key : ∀ (φ : A ⊗ A ⟶ A) (φB : B ⊗ B ⟶ B), φB.left ≫ pr = pr' ≫ φ.left →
      (φ ▷ (U ⊗ S')).left ≫ i = i' ≫ φB.left := by
    intro φ φB hφ
    apply hp.hom_ext
    · rw [Category.assoc, hi₁, Category.assoc, hφ, ← Category.assoc, hi'₁, ← Over.comp_left, ← Over.comp_left,
        whiskerRight_fst]
    · rw [Category.assoc, hi₂, Category.assoc, Over.w φB, hi'₂, ← Category.assoc, ← Over.comp_left,
        whiskerRight_snd]
  have ev : ∀ φ : A ⊗ A ⟶ A, CechPic.pull (φ ▷ (U ⊗ S')).left (cls N hN) =
      evc hN (fst (A ⊗ A) (U ⊗ S') ≫ φ) (snd (A ⊗ A) (U ⊗ S')) := fun φ ↦ by
    have : φ ▷ (U ⊗ S') = lift (fst (A ⊗ A) (U ⊗ S') ≫ φ) (snd (A ⊗ A) (U ⊗ S')) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, lift_fst]
      · rw [whiskerRight_snd, lift_snd]
    rw [this]; rfl
  have hm : fst (A ⊗ A) (U ⊗ S') ≫ μ[A] =
      (fst (A ⊗ A) (U ⊗ S') ≫ fst A A) * (fst (A ⊗ A) (U ⊗ S') ≫ snd A A) := by
    rw [← MonObj.comp_mul]
    congr 1
    show μ[A] = lift (fst A A) (snd A A) ≫ μ[A]
    rw [lift_fst_snd, Category.id_comp]
  have add : CechPic.pull (μ[A] ▷ (U ⊗ S')).left (cls N hN) =
      CechPic.pull (fst A A ▷ (U ⊗ S')).left (cls N hN) + CechPic.pull (snd A A ▷ (U ⊗ S')).left (cls N hN) := by
    rw [ev, ev, ev, hm]
    exact (isAdditive_iff hN).1 hadd _ _ _ _
  obtain ⟨c', hc'⟩ := hAb C (J.map σ) hJ' B g hB hBg _ _ i i' _ _ _ th th' (key _ _ hμ) (key _ _ h₁) (key _ _ h₂)
    (cls N hN) add
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : (A ⊗ U).left ⟶ B.left, k ≫ pr = (fst A U).left ∧ k ≫ B.hom = (snd A U).left :=
    ⟨hp.lift _ _ (by rw [Over.w, Over.w]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  refine ⟨CechPic.pull k c', ?_⟩
  have hk : (A ◁ fst U S').left ≫ k = i := by
    apply hp.hom_ext
    · rw [Category.assoc, hk₁, hi₁, ← Over.comp_left, whiskerLeft_fst]
    · rw [Category.assoc, hk₂, hi₂, ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  rw [← pull_comp, hk, hc']

theorem main : AbLift → ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (C : Type) [CommRing C] (σ : R →+* C) (N : LB (A ⊗ (Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)))).left) (hN : N.IsLB), IsAdditive N → ∃ c : Pic (A ⊗ Over.mk (spMap σ)).left, GlobalTheory.CechPic.pull (A ◁ fst (Over.mk (spMap σ)) (Over.mk (spMap (Ideal.Quotient.mk J)))).left c = cls N hN := fun hAb R _ J hJ A _ g hA hg C _ σ N hN hadd ↦
  finiteRing_sq_sub_mul_sq_eq_of_card hAb R J hJ A g hA hg C σ N hN hadd

end GlobalTheory.AddFamLift
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (frobR p R hR)) π → ∃ F : A ⟶ A₁, IsMonHom F ∧ F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A) := by
  first | exact @GlobalTheory.RelFrobGrp.main | exact GlobalTheory.RelFrobGrp.main | (intros; apply GlobalTheory.RelFrobGrp.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem UnitAt.zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {s : X.functionField} (hs : UnitAt x s) (n : ℤ) :
    UnitAt x (s ^ n) := by
  obtain ⟨u, rfl⟩ := hs
  refine ⟨u ^ n, ?_⟩
  have := congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map] at this
  exact this

theorem UnitAt.prod {X : Scheme.{0}} [IsIntegral X] {x : X} {ι : Type} (s : Finset ι) (f : ι → X.functionField)
    (h : ∀ b ∈ s, UnitAt x (f b)) : UnitAt x (∏ b ∈ s, f b) :=
  Finset.prod_induction f (UnitAt x) (fun _ _ => UnitAt.mul) ⟨1, by simp⟩ h

theorem eq_of_specializes_of_coheight {X : Scheme.{0}} {x y : X} (h : y ⤳ x) (hx : Order.coheight x = 1)
    (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  have hlt : x < y := lt_of_le_not_ge (show x ≤ y from h) fun h' => hne (h.antisymm (show x ⤳ y from h')).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [hx, hy] at this
  exact absurd this (by decide)

theorem unitAt_constFn {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ Sp R) (x : X) (b : R)
    (hb : b ∉ (q x).asIdeal) : IsUnit (X.presheaf.germ ⊤ x trivial (constFn q ⊤ b)) := by
  rw [← Scheme.mem_basicOpen_top, constFn_top, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hb

theorem exists_const_mul_unitAt_coheight_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (κ : K →+* X.functionField), (∀ b : R, κ (algebraMap R K b) = X.presheaf.germ ⊤ (genericPoint X) trivial (constFn q ⊤ b)) → ∀ (I : Type) (U : I → X.Opens) (t : I → X.functionField), (∀ x, ∃ i, x ∈ U i) → (∀ i x, x ∈ U i → t i ≠ 0) → (∀ i j x (s : X.functionField), x ∈ U i → x ∈ U j → GlobalTheory.VerticalUnit.UnitAt x (s * t j) → GlobalTheory.VerticalUnit.UnitAt x (s * t i)) → (∀ x, (q x).asIdeal = ⊥ → ∃ i, x ∈ U i ∧ GlobalTheory.VerticalUnit.UnitAt x (t i)) → ∃ a : Kˣ, ∀ i x, x ∈ U i → Order.coheight x = 1 → GlobalTheory.VerticalUnit.UnitAt x (κ a * t i) := by
  intro R K _ _ _ _ _ _ _ X _ _ q _ _ κ hκ I U t hcov ht0 htr hgen
  classical
  have hgz : GeneralizingMap q := Flat.generalizingMap q
  have hinj := IsFractionRing.injective R K
  have hunit : ∀ (x : X) (b : R), b ∉ (q x).asIdeal → UnitAt x (κ (algebraMap R K b)) := fun x b hb =>
    ⟨(unitAt_constFn q x b hb).unit, by
      rw [IsUnit.unit_spec, hκ]
      exact X.presheaf.germ_stalkSpecializes_apply _ _ _⟩
  let S : Set X := {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
  have hS : IsOpen S := by
    change IsOpen {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => (U i).isOpen.inter (isOpen_unitAt _)
  have hg : genericPoint X ∈ S := by
    let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, -, hy⟩ := hgz ((PrimeSpectrum.le_iff_specializes p₀ (q (genericPoint X))).1 bot_le)
    exact (genericPoint_specializes y).mem_open hS (hgen y (by rw [hy]))
  have hB := GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint X S hS hg
  set B : Set X := {x : X | Order.coheight x = 1 ∧ x ∉ S} with hBdef
  have key : ∀ b ∈ B, ∃ π : R, Prime π ∧ (q b).asIdeal = Ideal.span {π} ∧
      (∀ x : X, (q x).asIdeal = Ideal.span {π} → b ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk b) ∧
      Irreducible (X.presheaf.germ ⊤ b trivial (constFn q ⊤ π)) := by
    rintro b ⟨h1, hbS⟩
    have hb0 : (q b).asIdeal ≠ ⊥ := fun h => hbS (hgen b h)
    obtain ⟨π, hπ, hqb⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz b h1.le hb0
    obtain ⟨ξ, -, hξ, hd, hirr⟩ := GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime R X q π hπ
    have hξ1 : Order.coheight ξ = 1 := by
      have e := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk ξ)
      rw [ringKrullDim_stalk_eq_coheight] at e
      exact_mod_cast e
    obtain rfl : b = ξ := eq_of_specializes_of_coheight (hξ b hqb) h1 hξ1
    exact ⟨π, hπ, hqb, hξ, hd, hirr⟩
  choose! π hπ hqπ hsp hdvr hirr using key
  have hstar : ∀ b ∈ B, ∀ x : X, Order.coheight x = 1 → π b ∈ (q x).asIdeal → x = b := by
    intro b hb x hx hmem
    have hx0 : (q x).asIdeal ≠ ⊥ := fun h => (hπ b hb).ne_zero (by rw [h, Ideal.mem_bot] at hmem; exact hmem)
    obtain ⟨π', hπ', hqx⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz x hx.le hx0
    have hdvd : π' ∣ π b := Ideal.mem_span_singleton.1 (hqx ▸ hmem)
    have hq : (q x).asIdeal = Ideal.span {π b} :=
      hqx.trans (Ideal.span_singleton_eq_span_singleton.2 (hπ'.associated_of_dvd (hπ b hb) hdvd))
    exact eq_of_specializes_of_coheight (hsp b hb x hq) hx hb.1
  have hne : ∀ b ∈ B, algebraMap R K (π b) ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).2 (hπ b hb).ne_zero
  have key2 : ∀ b ∈ B, ∃ (i : I) (n : ℤ), b ∈ U i ∧ UnitAt b (κ (algebraMap R K (π b)) ^ (-n) * t i) := by
    intro b hb
    obtain ⟨i, hi⟩ := hcov b
    have := hdvr b hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (hirr b hb) (ht0 i b hi)
    have e : algebraMap _ X.functionField (X.presheaf.germ ⊤ b trivial (constFn q ⊤ (π b))) =
        κ (algebraMap R K (π b)) := by
      rw [hκ]; exact X.presheaf.germ_stalkSpecializes_apply _ _ _
    have hπ' : κ (algebraMap R K (π b)) ≠ 0 := (map_ne_zero κ).2 (hne b hb)
    refine ⟨i, n, hi, u, ?_⟩
    rw [hu, e, Units.smul_def, Algebra.smul_def, mul_left_comm, ← zpow_add₀ hπ', neg_add_cancel, zpow_zero,
      _root_.mul_one]
  have : Nonempty I := ⟨(hcov (genericPoint X)).choose⟩
  choose! ib n hUi hunitb using key2
  let F := hB.toFinset
  let a : Kˣ := ∏ b ∈ F.attach, (Units.mk0 _ (hne b.1 (hB.mem_toFinset.1 b.2))) ^ (-n b.1)
  have hκa : κ (a : K) = ∏ b ∈ F, κ (algebraMap R K (π b)) ^ (-n b) := by
    simp only [a, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
    exact Finset.prod_attach F (fun b => κ (algebraMap R K (π b)) ^ (-n b))
  refine ⟨a, fun i x hx h1 => ?_⟩
  rw [hκa]
  have hother : ∀ b ∈ F, b ≠ x → UnitAt x (κ (algebraMap R K (π b)) ^ (-n b)) := fun b hb hbx =>
    (hunit x (π b) fun hm => hbx (hstar b (hB.mem_toFinset.1 hb) x h1 hm).symm).zpow _
  by_cases hxS : x ∈ S
  · obtain ⟨j, hj, hu⟩ := hxS
    refine htr i j x _ hx hj ((UnitAt.prod F _ fun b hb => hother b hb ?_).mul hu)
    rintro rfl
    exact (hB.mem_toFinset.1 hb).2 ⟨j, hj, hu⟩
  · have hxB : x ∈ B := ⟨h1, hxS⟩
    have hxF : x ∈ F := hB.mem_toFinset.2 hxB
    rw [← Finset.mul_prod_erase F (fun b => κ (algebraMap R K (π b)) ^ (-n b)) hxF]
    refine htr i (ib x) x _ hx (hUi x hxB) ?_
    rw [mul_comm (κ (algebraMap R K (π x)) ^ (-n x)), mul_assoc]
    exact (UnitAt.prod _ _ fun b hb => hother b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)).mul
      (hunitb x hxB)

end GlobalTheory.VerticalUnit
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.ConjPoint

lemma IsConj.mem_lattice_iff {L L' : PeriodPair} {σ : ℂ ≃+* ℂ} {t t' : ℂ}
    (h : IsConj L L' σ t t') : t ∈ L.lattice ↔ t' ∈ L'.lattice := by
  rcases h with h | h
  · exact iff_of_true h.1 h.2
  · exact iff_of_false h.1 h.2.1

theorem exists_equiv_kerReps_isConj :
    ∀ (L : PeriodPair) (σ : ℂ ≃+* ℂ) (α : ℂ) (S S' : Finset ℂ), L.g₂ = σ L.g₂ → L.g₃ = σ L.g₃ →
      MulStable L α → IsKerReps L α S → IsKerReps L (σ α) S' →
      ∃ e : S ≃ S', ∀ t : S, GlobalTheory.ConjPoint.IsConj L L σ (t : ℂ) (e t : ℂ) := by
  intro L σ α S S' h₂ h₃ hα hS hS'
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  have hf : ∀ t : S, ∃ t' : S', IsConj L L σ (t : ℂ) (t' : ℂ) := by
    intro t
    obtain ⟨u, hu⟩ := latticePoint_surjective L (s (latticePoint L t))
    have h := (hc _ _).2 hu.symm
    obtain ⟨P, hP, hd⟩ := hS'.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.1 (hS.1 t t.2).1)
      (fun hm ↦ (hS.1 t t.2).2 (h.mem_lattice_iff.2 hm))
    exact ⟨⟨P, hP⟩, (hc _ _).2 (hu.symm.trans ((latticePoint_eq_iff L).2 hd))⟩
  choose f hf using hf
  refine ⟨Equiv.ofBijective f ⟨fun a b hab ↦ ?_, fun t' ↦ ?_⟩, hf⟩
  · have ha := (hc _ _).1 (hf a)
    have hb := (hc _ _).1 (hf b)
    rw [hab, ← hb] at ha
    exact Subtype.ext (hS.2.1 _ a.2 _ b.2 ((latticePoint_eq_iff L).1 (s.injective ha)))
  · obtain ⟨Q, hQ⟩ := s.surjective (latticePoint L t')
    obtain ⟨u, rfl⟩ := latticePoint_surjective L Q
    have h := (hc _ _).2 hQ
    obtain ⟨P, hP, hd⟩ := hS.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.2 (hS'.1 t' t'.2).1)
      (fun hm ↦ (hS'.1 t' t'.2).2 (h.mem_lattice_iff.1 hm))
    refine ⟨⟨P, hP⟩, Subtype.ext (hS'.2.1 _ (f _).2 _ t'.2 ((latticePoint_eq_iff L).1 ?_))⟩
    rw [← (hc _ _).1 (hf ⟨P, hP⟩), ← hQ, (latticePoint_eq_iff L).2 hd]

end GlobalTheory.ConjPoint
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.TorsMemVal

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

theorem mem_of_val (V : ValuationSubring ℂ) {n u Ω x : ℂ} (k : ℕ) (hn : V.valuation n = 1)
    (hu : V.valuation u = V.valuation Ω) (h : n ^ k * x / Ω ^ k ∈ V) : x / u ^ k ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu] at h
  rwa [map_div₀, map_pow]

theorem main : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → ∀ z w, z ∉ L.lattice → w ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (N : ℂ) * w ∈ L.lattice → L.derivWeierstrassP z / u ^ 3 ∈ V ∧ (L.weierstrassP z - L.weierstrassP w) / u ^ 2 ∈ V := by
  intro L β u V N hβ hβi hu hN z w hz hw hNz hNw
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (n := 12) (by norm_num)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN
    · exact h
  have huΩ : V.valuation u = V.valuation Ω := by
    rw [← hΩ, map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have h := GlobalTheory.WpFam.LatTorsVal.main L β Ω N hβ hβi (hΩ.trans (latticeCurve_Δ L)) hN0
  exact ⟨mem_of_val V 3 hN huΩ (mem_of_isIntegral V (h.1 z hNz).2),
    mem_of_val V 2 hN huΩ (mem_of_isIntegral V (h.2 z w hz hw hNz hNw))⟩

end GlobalTheory.CMModel.TorsMemVal
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem isMinimal_of_discr_eq_unit_mul_neg_cube : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (W : WeierstrassCurve F) (u : (w.valuationSubringAtPrime F)ˣ), (p : 𝓞 F) ∉ w.asIdeal ^ 3 → W.IsIntegral (w.valuationSubringAtPrime F) → W.Δ = ((u : w.valuationSubringAtPrime F) : F) * -(p : F) ^ 3 → W.IsMinimal (w.valuationSubringAtPrime F) := by
  intro p F _ _ w W u hp hI hΔ
  have hmem : ∀ y : F, y ∈ w.valuationSubringAtPrime F ↔ w.valuation F y ≤ 1 := by
    intro y
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    rfl
  refine GlobalTheory.isMinimal_of_forall_div_pow_twelve _ F W hI ?_
  intro x hx0 hx
  by_contra hnu
  have hxF : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hx1 : w.valuation F (x : F) < 1 := by
    refine lt_of_le_of_ne ((hmem _).1 x.2) (fun h => hnu ?_)
    have hi : (x : F)⁻¹ ∈ w.valuationSubringAtPrime F := by
      rw [hmem, map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hxF))
  have hu : w.valuation F ((u : w.valuationSubringAtPrime F) : F) = 1 := by
    have h1 := (hmem _).1 (u : w.valuationSubringAtPrime F).2
    have h2 := (hmem _).1 ((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F).2
    have h3 : w.valuation F ((u : w.valuationSubringAtPrime F) : F) *
        w.valuation F (((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F) : F) = 1 := by
      rw [← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]; simp
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ _ * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  obtain ⟨y, hy⟩ := hx
  have hy1 := (hmem _).1 y.2
  have hyx : (y : F) * (x : F) ^ 12 = W.Δ := by
    have : (y : F) = W.Δ / (x : F) ^ 12 := hy
    rw [this]; field_simp
  have hv := congrArg (w.valuation F) (hyx.trans hΔ)
  rw [map_mul, map_mul, hu, Valuation.map_neg, map_pow, map_pow, one_mul] at hv
  have hpv : w.valuation F (p : F) = w.intValuation (p : 𝓞 F) := by
    rw [← w.valuation_of_algebraMap (K := F)]; simp
  have hp' : WithZero.exp (-(3 : ℤ)) < w.valuation F (p : F) := by
    rw [hpv]
    by_contra h
    exact hp ((w.intValuation_le_pow_iff_mem _ 3).1 (by simpa using h))
  have hle : w.valuation F (p : F) ^ 3 ≤ w.valuation F (x : F) ^ 12 := by
    rw [← hv]
    calc _ ≤ 1 * _ := mul_le_mul_left hy1 _
      _ = _ := one_mul _
  have hvx0 : w.valuation F (x : F) ≠ 0 := by simpa using hxF
  have hvp0 : w.valuation F (p : F) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  rw [← WithZero.exp_log hvx0] at hle hx1
  rw [← WithZero.exp_log hvp0] at hle hp'
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_le_exp] at hle
  rw [WithZero.exp_lt_exp] at hp'
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx1
  simp only [nsmul_eq_mul] at hle
  push_cast at hle
  omega

end GlobalTheory.CMModel
end

section

open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrdLift

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem mul_mem_intA {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hx : x ∈ GlobalTheory.PlaceComp.intA F E)
    (hy : y ∈ GlobalTheory.PlaceComp.intA F E) : x * y ∈ GlobalTheory.PlaceComp.intA F E :=
  by apply _root_.UpperTheory.Reformulated.B.Uc13.mul_mem_intA <;> assumption

end GlobalTheory.OrdLift

theorem GlobalTheory.OrdLift.ordAt_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E),
    a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  intro F E _ _ _ _ _ v a ha
  induction ha using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b ⊗ₜ[F] (x : E),
      AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf F v ⟨b, hb⟩, x, rfl⟩, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b) ⊗ₜ[F] (x : E) = _
    rw [GlobalTheory.SplitIdem.evalV_singleV_same]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | one =>
    refine ⟨1, AddSubgroup.subset_closure ⟨1, GlobalTheory.OrdLift.one_mem_intAf F, 1, ?_⟩, map_one _⟩
    simp [Algebra.TensorProduct.one_def]
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s + t, add_mem hs ht, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨-s, neg_mem hs, map_neg _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, GlobalTheory.OrdLift.mul_mem_intA F E hs ht, map_mul _ _ _⟩

end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable : ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L → L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  first | exact @GlobalTheory.CMModel.integersLattice_invariants_ne_zero | exact GlobalTheory.CMModel.integersLattice_invariants_ne_zero | (intros; apply GlobalTheory.CMModel.integersLattice_invariants_ne_zero <;> assumption)
end
