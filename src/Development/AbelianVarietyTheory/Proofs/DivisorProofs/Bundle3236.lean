module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3196
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryOfPoint
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_of_mumfordBundle_torsion_presentations : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (D : DegPre V) {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (P : LB (G2 B).left), P.IsLB → ∀ (t : Sp V ⟶ S) (a₁ a₂ : D.P.A.left ⟶ B.left) (aa₁ aa₂ : (G2 D.P.A).left ⟶ (G2 B).left), IsGrpPullback D.P.A B t a₁ → IsGrpPullback D.P.A B t a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₁) → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₂) → ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], (∀ x : TF (R := V) F ⟶ D.P.A, x ^ n = 1 → x.left ≫ a₁ = x.left ≫ a₂) → a₁ = a₂ := by
  first | exact @GlobalTheory.PresRigid.eq_of_lam_of_torsion | exact GlobalTheory.PresRigid.eq_of_lam_of_torsion | (intros; apply GlobalTheory.PresRigid.eq_of_lam_of_torsion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.cubicalProduct_identity_of_genericPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b cχ : 𝟙_ (Over (Sp V)) ⟶ D.P.A),
    b ^ N = 1 → ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit (TF (R := V) (FractionRing V)) ≫ cχ)
        (toUnit (TF (R := V) (FractionRing V)) ≫ b ^ i) (toUnit (TF (R := V) (FractionRing V)) ≫ b) =
      val χt (toUnit (TF (R := V) (FractionRing V))).left z J ^ N) →
    ∀ (T : Over (Sp V)) (z : T.left) J, Good D.P.L z J →
      ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit T ≫ cχ) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χt T.hom z J ^ N := by
  first | exact @GlobalTheory.Poinc.Sep.CubInt.cubProd_of_generic | exact GlobalTheory.Poinc.Sep.CubInt.cubProd_of_generic | (intros; apply GlobalTheory.Poinc.Sep.CubInt.cubProd_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X, (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  first | exact @GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine | exact GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine | (intros; apply GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torusExtension_torsion_lift_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℕ), 1 ≤ n → ∀ (c' : D.X → (𝟙_ (Over (Sp R)) ⟶ D.P.A)), (∀ χ, c' χ ^ n = D.c χ) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A), b ^ n = 1 → ∃ p : QkPt D F n, p.y = 0 ∧ p.g.b = b := by
  first | exact @GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq | exact GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq | (intros; apply GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.galois_invariant_point_descends_to_section : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first | exact @GlobalTheory.FinDescent.galoisFixed_point_of_finite | exact GlobalTheory.FinDescent.galoisFixed_point_of_finite | (intros; apply GlobalTheory.FinDescent.galoisFixed_point_of_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_translates_cover_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : G.left.Opens), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → ∀ x : G.left, ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, (𝟙 G * (toUnit G ≫ a)).left x ∈ O := by
  first | exact @GlobalTheory.Mum.Cover.exists_section_translate_mem | exact GlobalTheory.Mum.Cover.exists_section_translate_mem | (intros; apply GlobalTheory.Mum.Cover.exists_section_translate_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_exists_comp_eq_nsmul_of_kernel_killed : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (l : A ⟶ B), IsMonHom l → ∀ e : ℕ, IsUnit (e : k) → (∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → x ^ e = 1) → ∃ m : B ⟶ A, IsMonHom m ∧ l ≫ m = 𝟙 A ^ e := by
  first | exact @GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed | exact GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed | (intros; apply GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_open_translations_moving_closedPoints_into_open : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (V : G.left.Opens), (∃ v ∈ V, G.hom v = closedPoint R) → ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R ∧ IsClosed ({x} : Set G.left)) → ∃ O : G.left.Opens, (∃ u ∈ O, G.hom u = closedPoint R) ∧ ∀ (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) (x a : Over.mk t ⟶ G), (∀ z, x.left z ∈ s) → (∀ z, a.left z ∈ O) → ∀ z, (x * a).left z ∈ V := by
  first | exact @GlobalTheory.Mum.exists_open_mul_mem | exact GlobalTheory.Mum.exists_open_mul_mem | (intros; apply GlobalTheory.Mum.exists_open_mul_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.exists_generator_transport_down_lineBundleIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Ix : Type} [Fintype Ix]
    (w : LB.Iso L' (L.pull F)), w.IsGen → L.IsLB → L'.IsLB → ∀ (φ' : Ix → (Y ⟶ X')) (ε : Ix → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t.IsGen ∧ PMaps w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) := by
  first | exact @GlobalTheory.GenTransport.exists_gen_down_pmaps | exact GlobalTheory.GenTransport.exists_gen_down_pmaps | (intros; apply GlobalTheory.GenTransport.exists_gen_down_pmaps <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.determinantCondition_spreads_from_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (act : OAct (𝓞 E) G) (ρ : A), IsAbelianScheme G → ρ ^ 2 = -(H.d : A) → Nonempty (ℚ →+* A) → ∀ (K₀ : Type) [Field K₀] [IsAlgClosed K₀] (g₀ : A →+* K₀), DetCond D act (spMap g₀) (g₀ ρ) → ∀ (K : Type) [Field K] [IsAlgClosed K] (g : A →+* K), DetCond D act (spMap g) (g ρ) := by
  first | exact @GlobalTheory.SpreadOnePoint.detCond_of_point | exact GlobalTheory.SpreadOnePoint.detCond_of_point | (intros; apply GlobalTheory.SpreadOnePoint.detCond_of_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  first | exact @GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | exact GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | (intros; apply GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_levelIsometry_of_point_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (A : Type) [CommRing A] [IsDomain A] (P : Out.PolAV (Sp A)) (act : 𝓞 E → (P.A ⟶ P.A)) (z : A) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver (Sp A) ⟶ P.A)) (n m N : ℕ), 0 < n → 0 < N → Nonempty (ℚ →+* A) → z ^ N = 1 → (∀ i, pt i ^ N = 1) → (∀ a, IsMonHom (act a)) → (∃ (K : Type) (_ : Field K) (β : A →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : A →+* K), ∃ (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i := by
  first | exact @GlobalTheory.exists_levelIsometry_of_point | exact GlobalTheory.exists_levelIsometry_of_point | (intros; apply GlobalTheory.exists_levelIsometry_of_point <;> assumption)
end
