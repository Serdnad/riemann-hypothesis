module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalSymmetricLineBundleTwoTors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.uniformisedEighthPower_endomorphism_acts_by_intMatrix : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  first | exact @GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | exact GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | (intros; apply GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.semiAbelian_uniformising_eighthPower_isPower_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  first | exact @GlobalTheory.Poinc.Sep.unif_pow_isPow_model | exact GlobalTheory.Poinc.Sep.unif_pow_isPow_model | (intros; apply GlobalTheory.Poinc.Sep.unif_pow_isPow_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cubicalStructureMap_of_lineBundleIso_rescaled : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) → Function.Surjective (G3 G').hom.appTop.hom → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'), LBIso P'.L.L (P.L.L.pull F) → ∃ w, GlobalTheory.UU.IsCPMap P' P f F hw w := by
  first | exact @GlobalTheory.PkgBaseChange.exists_isCPMap_of_lbIso | exact GlobalTheory.PkgBaseChange.exists_isCPMap_of_lbIso | (intros; apply GlobalTheory.PkgBaseChange.exists_isCPMap_of_lbIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cubicalTrivialisation_splitTorus_field : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  first | exact @GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | exact GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | (intros; apply GlobalTheory.Mum.TorusCubTriv.exists_cubTriv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_even_cubicalTriv_translate_order_two : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  first | exact @GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | exact GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | (intros; apply GlobalTheory.TranslateEvenTriv.exists_even_cubTriv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_translate_cubicalSymmetricLineBundle_twoTorsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (a : 𝟙_ (Over S) ⟶ G),
    a ^ 2 = 1 → ∀ ρ : LB.Gen (P.L.L.pull a.left), ρ.IsGen →
    ∃ P' : GlobalTheory.UU.CP G, P'.L.L = P.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left ∧
      (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P'.sym x.left z J' =
          val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹) ∧
      (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P'.c z J' x y u = cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹) := by
  first | exact @GlobalTheory.TranslCP.exists_transl | exact GlobalTheory.TranslCP.exists_transl | (intros; apply GlobalTheory.TranslCP.exists_transl <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_adic_sum_field_of_coeff_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Jx : Type) [Fintype Jx] (g : Jx → F) (Ix : Type) (c : Ix → Jx → R), (∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ maximalIdeal R ^ n}.Finite) → ∃ s : F, GlobalTheory.UT.SumF (maximalIdeal R) F (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k) s := by
  first | exact @GlobalTheory.Mum.exists_sumF_of_coeff | exact GlobalTheory.Mum.exists_sumF_of_coeff | (intros; apply GlobalTheory.Mum.exists_sumF_of_coeff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  first | exact @GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | exact GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | (intros; apply GlobalTheory.Poinc.IntTerm.psi_zero_rig_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  first | exact @GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | exact GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | (intros; apply GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.PhiLinear

theorem exists_linear_phi : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  intro R _ _ _ I _ D F _ _ _ N hN p w hw
  exact ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of_globalFns GlobalTheory.globalFns_holds R I D F N hN.pos p w hw.1

end GlobalTheory.Mum.PhiLinear
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem torusHomOf_iff_charUnit {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem charUnit_eq_pointsEquiv {S : Scheme.{0}} {X : Type} [AddCommGroup X] (χ : X) :
    charUnit S X χ = GlobalTheory.splitTorusPointsEquiv S X _ (𝟙 _) (Multiplicative.ofAdd χ) :=
  Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) χ).trans (GlobalTheory.SplitTorusHom.appTop_id _)).symm

theorem torusHomOf_prod_zpow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {K : Type}
    [Fintype K] (n : K → ℤ) (h : K → X' → X) (t : K → (splitTorus S X ⟶ splitTorus S X'))
    (ht : ∀ i, TorusHomOf (h i) (t i)) : TorusHomOf (fun χ => ∑ i, n i • h i χ) (∏ i, t i ^ n i) := by
  simp only [torusHomOf_iff_charUnit] at ht
  rw [torusHomOf_iff_charUnit]
  intro χ
  have e₁ : ∀ i, GlobalTheory.splitTorusPointsEquiv S X' _ (t i) (Multiplicative.ofAdd χ) = charUnit S X (h i χ) := fun i =>
    Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X' _ (t i) χ).trans (ht i χ))
  rw [← GlobalTheory.splitTorusPointsEquiv_val, map_prod]
  simp only [map_zpow]
  rw [charUnit_eq_pointsEquiv, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow, ← charUnit_eq_pointsEquiv]
  congr 1
  change (MonoidHom.eval (Multiplicative.ofAdd χ)) (∏ x, GlobalTheory.splitTorusPointsEquiv S X' _ (t x) ^ n x) = _
  rw [map_prod]
  simp only [map_zpow, MonoidHom.eval, MonoidHom.flip_apply, MonoidHom.id_apply, e₁]

end GlobalTheory.Mum.PowData

theorem GlobalTheory.Mum.PowData.onTorus_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (h : K → D₀.toPre.X → D.toPre.X), (∀ i, OnTorus U U₀ (a i) (h i)) → OnTorus U U₀ (∏ i, a i ^ n i) (fun χ => ∑ i, n i • h i χ) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a h H e
  choose t ht et using fun i => H i e
  refine ⟨∏ i, t i ^ n i, torusHomOf_prod_zpow n h t ht, ?_⟩
  have := (U₀.gt e).i_hom
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  have hm : (Over.pullback (thick R I e)).map (∏ i, a i ^ n i) = ∏ i, (Over.pullback (thick R I e)).map (a i) ^ n i :=
    (map_prod ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _).trans
      (Finset.prod_congr rfl fun i _ => map_zpow ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _)
  rw [hm, comp_prod_zpow, prod_zpow_comp]
  exact Finset.prod_congr rfl fun i _ => by rw [et i]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.morphismToProjSpace_sectionPullback_comp : ∀ (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X) (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R) (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤) (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤), GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ = GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ := by
  first | exact @GlobalTheory.Mum.toProj_secPull_secPull | exact GlobalTheory.Mum.toProj_secPull_secPull | (intros; apply GlobalTheory.Mum.toProj_secPull_secPull <;> assumption)
end
