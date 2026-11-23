module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.heckeCharacter_bounded_conductor_kills_idele_norms : ∀ (D : D7) (χ : HChar D.host.E) (n : D.what₂.Tau → ℤ) (S : Finset ℕ) (k : ℕ), χ.TrivOn D.host.F → χ.HasInf (embT D) n → (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  first | exact @GlobalTheory.NormKill.chi_finIdl_norm_eq_one | exact GlobalTheory.NormKill.chi_finIdl_norm_eq_one | (intros; apply GlobalTheory.NormKill.chi_finIdl_norm_eq_one <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.heckeCharacter_nonInert_bounded_level_kills_units : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime ∧ ¬ InertQ D q) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1 := by
  first | exact @GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt | exact GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt | (intros; apply GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.unramified_eta_character_kills_finite_idele_norm : ∀ (D : D7) (χ : HChar D.host.E), Formalism.L2.Host.IsEtaT D.host χ → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  first | exact @GlobalTheory.EtaTildeNorm.map_finIdl_norm | exact GlobalTheory.EtaTildeNorm.map_finIdl_norm | (intros; apply GlobalTheory.EtaTildeNorm.map_finIdl_norm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
noncomputable section
namespace GlobalTheory.RiemannExists

theorem exists_sym_translate : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L → ∃ (L' : LB B.left) (hL' : L'.IsLB), Out.Rigidified B L' ∧ Out.Sym B L' ∧ Out.RelAmple B L' ∧ Out.KTriv B L' ∧ lam (cls L' hL') (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) := by
  intro K _ _ B _ hB L hL ha hk
  have := hB.comm
  obtain ⟨c, hc⟩ := exists_gen_theta_of_isAbelianScheme K B hB L hL
  have hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen := ⟨c, hc⟩
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL)
  have hlam : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, CechPic.lam_pull, ← Hom.inv_def, ← Hom.inv_def,
      FormPoly.lam_inv_left hL hΘ, FormPoly.lam_inv_right hL hΘ, neg_neg, sub_self]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda K B hB L hL hk O hO hlam
  obtain ⟨a, hab⟩ := SS.SemiDivisible.pow_surj_abelian K B hB (n := 2) (by norm_num) b
  have hL' : (RigidTranslate.rigTransl L a).IsLB := DVR.linComb_isLB _ hL _ _
  refine ⟨_, hL', RigidTranslate.rigidified_rigTransl hL, GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect K B L hL hΘ a (by rw [← eO, hb, hab]),
    GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint K B hB L hL a ha, GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle _ B L hL a hk, ?_⟩
  have e := (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2
    (RigidTranslate.lam_rigTransl (t := a) hL c hc)
  rw [CechPic.cls_pull (LB.isLB_linComb hL _ _), CechPic.pull_id] at e
  exact (CechPic.cls_cube_two hL' _ _ _).symm.trans (e.trans (CechPic.cls_cube_two hL _ _ _))

end GlobalTheory.RiemannExists
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeMixed

open GlobalTheory.CechPic

theorem lam_zpow_left {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℤ) :
    lam (cls L hL) (x ^ n) z = n • lam (cls L hL) x z := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
    exact lam_pow_left hL hΘ x z k
  | negSucc k =>
    have h := lam_mul_left hL hΘ (x ^ (k + 1)) (x ^ (k + 1))⁻¹ z
    rw [mul_inv_cancel, lam_one_left, lam_pow_left hL hΘ] at h
    rw [zpow_negSucc, negSucc_zsmul]
    exact eq_neg_of_add_eq_zero_right h.symm

theorem lam_zpow_zpow {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) (m n : ℤ) :
    lam (cls L hL) (x ^ m) (y ^ n) = (m * n) • lam (cls L hL) x y := by
  rw [lam_zpow_left hL hΘ, lam_comm, lam_zpow_left hL hΘ, lam_comm, smul_smul]

theorem pull_one_eq_zero {K : Type} [Field K] {A T : Over (Sp K)} [GrpObj A] (c : CechPic.Pic A.left) :
    CechPic.pull (1 : T ⟶ A).left c = 0 := by
  change CechPic.pull ((toUnit T).left ≫ (η : 𝟙_ (Over (Sp K)) ⟶ A).left) c = 0
  rw [pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) _ c, map_zero]

theorem mixed_mul : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  intro K _ A _ hA L hL T x y m n a b
  have : IsCommMonObj A := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have key : ∀ (c : CechPic.Pic A.left) (u v : T ⟶ A),
      CechPic.pull (u * v).left c = CechPic.pull u.left c + CechPic.pull v.left c + lam c u v := by
    intro c u v
    unfold lam
    rw [pull_one_eq_zero]
    abel
  rw [mul_inv, key, key, ← zpow_neg, ← zpow_neg, lam_zpow_zpow hL hΘ, lam_zpow_zpow hL hΘ, neg_mul_neg]
  module

end GlobalTheory.CubeMixed
end
end

section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  intro K _ A _ hA L hL T x y m n a b
  have : IsCommMonObj A := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have lam_zpow_left (x z : T ⟶ A) (n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ n) z =
        n • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x z := by
    open GlobalTheory.CechPic in
    cases n with
    | ofNat k =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
      exact lam_pow_left hL hΘ x z k
    | negSucc k =>
      have h := lam_mul_left hL hΘ (x ^ (k + 1)) (x ^ (k + 1))⁻¹ z
      rw [mul_inv_cancel, lam_one_left, lam_pow_left hL hΘ] at h
      rw [zpow_negSucc, negSucc_zsmul]
      exact eq_neg_of_add_eq_zero_right h.symm
  have lam_zpow_zpow (x y : T ⟶ A) (m n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ m) (y ^ n) =
        (m * n) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
    rw [lam_zpow_left, GlobalTheory.CechPic.lam_comm, lam_zpow_left,
      GlobalTheory.CechPic.lam_comm, smul_smul]
  have pull_one_eq_zero (c : GlobalTheory.CechPic.Pic A.left) :
      GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 := by
    change GlobalTheory.CechPic.pull ((toUnit T).left ≫ (η : 𝟙_ (Over (Sp K)) ⟶ A).left) c = 0
    rw [GlobalTheory.CechPic.pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) _ c, map_zero]
  have key : ∀ (c : GlobalTheory.CechPic.Pic A.left) (u v : T ⟶ A),
      GlobalTheory.CechPic.pull (u * v).left c = GlobalTheory.CechPic.pull u.left c +
        GlobalTheory.CechPic.pull v.left c + GlobalTheory.CechPic.lam c u v := by
    intro c u v
    unfold GlobalTheory.CechPic.lam
    rw [pull_one_eq_zero]
    abel
  rw [mul_inv, key, key, ← zpow_neg, ← zpow_neg, lam_zpow_zpow, lam_zpow_zpow, neg_mul_neg]
  module
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualTriv

theorem range_sub {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S) (p : Y ⟶ A)
    (hY : ∀ y, Y.hom y ∈ U) : Set.range p.left ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  show A.hom (p.left y) ∈ U
  rw [← Scheme.Hom.comp_apply, Over.w p]
  exact hY y

noncomputable def liftU {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι p.left (range_sub A U Y p hY)

theorem liftU_fac {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : liftU A U Y hY p ≫ (A.hom ⁻¹ᵁ U).ι = p.left :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.DualTriv

open GlobalTheory.DualTriv in
theorem GlobalTheory.twice_cls_eq_zero_of_translates_mem : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), A.hom ⁻¹ᵁ U ≤ W → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A), (∀ y, Y.hom y ∈ U) → (∀ y, v.left y ∈ V) → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → ∀ l : Y.left ⟶ W.toScheme, l ≫ W.ι = x.left → GlobalTheory.CechPic.pull l (2 • c) = 0 := by
  intro S _ A _ _ U V W hV hW c hc Y x a v hY hv hxa l hl
  set cU := GlobalTheory.CechPic.pull (A.left.homOfLE hW) c with hcU
  have zero_of : ∀ p : Y ⟶ A, (∀ y, p.left y ∈ V) →
      GlobalTheory.CechPic.pull (liftU A U Y hY p) cU = 0 := by
    intro p hp
    have H : Set.range p.left ⊆ Set.range V.ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hp y
    have e : liftU A U Y hY p ≫ A.left.homOfLE hW = IsOpenImmersion.lift V.ι p.left H ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
        liftU_fac, IsOpenImmersion.lift_fac]
    rw [hcU, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp, hc, map_zero]
  have s1 := GlobalTheory.T.square_theorem_pic_class_over_open S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) x a
  have s2 := GlobalTheory.T.square_theorem_pic_class_over_open S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) v a
  rw [zero_of _ (fun y => (hxa y).1), zero_of _ (fun y => (hxa y).2.1)] at s1
  rw [zero_of _ (fun y => (hxa y).2.2.1), zero_of _ (fun y => (hxa y).2.2.2), zero_of _ hv] at s2
  have two : 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU = 0 := by
    calc 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU
        = (2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) -
          (2 • (0 : GlobalTheory.CechPic.Pic _) + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) := by abel
      _ = 0 := by rw [← s1, ← s2, sub_self]
  have el : l = liftU A U Y hY x ≫ A.left.homOfLE hW := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, liftU_fac, hl]
  rw [map_nsmul, el, GlobalTheory.CechPic.pull_comp, ← hcU, two]
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.LogHermHess

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι]

def affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x : E) : ℂ :=
  ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (c j + L j x)

theorem hasFDerivAt_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x : E) :
    HasFDerivAt (fun y => c + L y) L x := L.hasFDerivAt.const_add c

theorem contDiff_aff (c : ℂ) (L : E →L[ℂ] ℂ) : ContDiff ℝ 2 (fun y => c + L y) :=
  contDiff_const.add (L.restrictScalars ℝ).contDiff

theorem contDiff_conj_aff (c : ℂ) (L : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (starRingEnd ℂ) (c + L y)) :=
  Complex.conjCLE.contDiff.comp (contDiff_aff c L)

theorem del_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : del (fun y => c + L y) x v = L v := by
  rw [del_eq_fderiv (hasFDerivAt_aff c L x).differentiableAt, (hasFDerivAt_aff c L x).fderiv]

theorem dbar_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : dbar (fun y => c + L y) x v = 0 := by
  rw [dbar_eq_zero (hasFDerivAt_aff c L x).differentiableAt]; rfl

theorem contDiff_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) :=
  ((contDiff_aff c L).mul contDiff_const).mul (contDiff_conj_aff c' L')

theorem del_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    del (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = L v * q * (starRingEnd ℂ) (c' + L' x) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [del_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    del_mul h1 (differentiableAt_const q), del_conj, dbar_aff, del_aff]
  simp

theorem dbar_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    dbar (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = (c + L x) * q * (starRingEnd ℂ) (L' v) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [dbar_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    dbar_mul h1 (differentiableAt_const q), dbar_conj, dbar_aff, del_aff]
  simp

theorem contDiff_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (affForm Q c L) :=
  ContDiff.sum fun _ _ => ContDiff.sum fun _ _ => contDiff_term _ _ _ _ _

theorem del_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    del (affForm Q c L) x v = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x) := by
  unfold affForm
  rw [del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => del_term _ _ _ _ _ _ _

theorem dbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    dbar (affForm Q c L) x v = ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j v) := by
  unfold affForm
  rw [dbar_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dbar_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => dbar_term _ _ _ _ _ _ _

theorem ddbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v w : E) :
    ddbar (affForm Q c L) x v w = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w) := by
  rw [ddbar_eq_del_dbar (contDiff_affForm Q c L).contDiffAt]
  have : (fun y => dbar (affForm Q c L) y w)
      = affForm Q c L ∘ id - affForm Q c L ∘ id + fun y => ∑ i, ∑ j,
        (c i + L i y) * Q i j * (starRingEnd ℂ) (L j w + (0 : E →L[ℂ] ℂ) y) := by
    funext y; simp [dbar_affForm]
  rw [this, sub_self, zero_add,
    del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [del_term]; simp

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem ofReal_re_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x : E) : ((affForm Q c L x).re : ℂ) = affForm Q c L x := by
  rw [← Complex.conj_eq_iff_re, affForm]

  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : (starRingEnd ℂ) (Q j i) = Q i j := hQ.apply i j
  rw [this]; ring

theorem leviForm_log_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x v w : E) (hx : affForm Q c L x ≠ 0) :
    leviForm (fun y => Real.log (affForm Q c L y).re) x v w
      = (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x
        - (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x))
          * (∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x ^ 2 := by
  have hre : (fun y => ((affForm Q c L y).re : ℂ)) = affForm Q c L :=
    funext (ofReal_re_affForm hQ c L)
  have hx' : (affForm Q c L x).re ≠ 0 := fun h => hx (by
    rw [← ofReal_re_affForm hQ c L x, h]; simp)
  have ht : ContDiffAt ℝ 2 (fun y => (affForm Q c L y).re) x :=
    (Complex.reCLM.contDiff.comp (contDiff_affForm Q c L)).contDiffAt
  rw [leviForm_real_comp (h := Real.log) (t := fun y => (affForm Q c L y).re)
    (Real.contDiffAt_log.2 hx') ht, leviForm, hre, ddbar_affForm, del_affForm, dbar_affForm,
    Real.deriv_log', deriv_inv]
  push_cast
  rw [ofReal_re_affForm hQ]
  ring

end General

theorem leviForm_log_herm : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2 := by
  intro n B _ _ e _ Q hQ u z hu h q hq hq0 a b
  let c : Option B → ℂ := fun i => Option.elim i 1 (fun a => z (e a))
  let L : Option B → (B → ℂ) →L[ℂ] ℂ := fun i => Option.elim i 0 (fun a => ContinuousLinearMap.proj a)
  let M : (B → ℂ) →L[ℂ] V n :=
    ∑ a, (ContinuousLinearMap.proj a : (B → ℂ) →L[ℂ] ℂ).smulRight (coordVec (e a))
  have hM : ∀ t, M t = ∑ a, t a • coordVec (e a) := fun t => by
    simp [M, ContinuousLinearMap.sum_apply]
  have hM1 : ∀ a, M (Pi.single a 1) = coordVec (e a) := fun a => by
    rw [hM]; simp [Pi.single_apply, ite_smul]
  have hφ : HasFDerivAt (fun t => z + M t) M 0 := M.hasFDerivAt.const_add z
  have h0 : z + M 0 = z := by simp
  have hc := leviForm_comp_holo (u := u) (φ := fun t => z + M t) (z := 0) (by rw [h0]; exact hu)
    (contDiff_const.add M.contDiff).contDiffAt (Pi.single a 1) (Pi.single b 1)
  rw [hφ.fderiv, hM1, hM1, h0] at hc
  have hw : ∀ (t : B → ℂ) i, Option.elim i 1 (fun a => z (e a) + t a) = c i + L i t := by
    intro t i; cases i <;> simp [c, L]
  have hf : (fun t => u (z + M t)) = fun t => Real.log (affForm Q c L t).re := by
    funext t
    rw [hM, h, affForm]
    simp only [hw]
    rfl
  have hq' : affForm Q c L 0 = q := by
    rw [hq, affForm]; simp [c]
  rw [← hc, hf, leviForm_log_affForm hQ _ _ _ _ _ (hq' ▸ hq0), hq']
  have hL : ∀ (a : B) i, L i (Pi.single a 1) = if i = some a then 1 else 0 := by
    intro a i; cases i <;> simp [L, Pi.single_apply]
  simp only [hL, map_zero, add_zero, apply_ite (starRingEnd ℂ), map_one, ite_mul, mul_ite, one_mul,
    zero_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  rfl

end GlobalTheory.LogHermHess
end
end

section

theorem GlobalTheory.Top.heckeTateFE : GlobalTheory.Published.HeckeTateFunctionalEquation :=
  GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation
end
