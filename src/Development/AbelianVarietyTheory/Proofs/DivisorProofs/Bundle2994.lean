module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.rigidified_symmetric_of_symmetric_fieldExtension_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  first | exact @GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension | exact GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension | (intros; apply GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SemiAbDesc.exists_grpPullback_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (G₁ : Over (Sp R)) [GrpObj G₁], IsSemiAbelian G₁ → ∀ (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X), y ≫ j = jK R ≫ ξ → ∀ (B : Over (Sp (FractionRing R))) [GrpObj B] (a : B.left ⟶ G₁.left) (b : B.left ⟶ A.left), IsGrpPullback B G₁ (jK R) a → IsGrpPullback B A y b → ∃ πC : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ πC ∧ a ≫ πC = b ≫ e := by
  intro R _ _ _ _ X S j A _ G _ e hG hA G₁ _ hG₁ ξ y hyj B _ a b ha hb
  have hBG : IsGrpPullback B G (jK R ≫ ξ) (b ≫ e) := (hb.comp hA).congr hyj rfl
  have hG₂ : IsGrpPullback ((Over.pullback ξ).obj G) G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hsG₂ : IsSemiAbelian ((Over.pullback ξ).obj G) := IsSemiAbelian.pullback ξ G hG
  have hw : (b ≫ e) ≫ G.hom = (B.hom ≫ jK R) ≫ ξ := by rw [hBG.1.w, Category.assoc]
  let i₂ : B.left ⟶ ((Over.pullback ξ).obj G).left := pullback.lift (b ≫ e) (B.hom ≫ jK R) hw
  have hi₂ : i₂ ≫ pullback.fst G.hom ξ = b ≫ e := pullback.lift_fst _ _ _
  have hBG₂ : IsGrpPullback B ((Over.pullback ξ).obj G) (jK R) i₂ :=
    hG₂.cancel (hBG.congr rfl hi₂.symm) (pullback.lift_snd _ _ _)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (ReciprocityTheory.ChartRestriction.G.Out.jK R) := .fractionField R (FractionRing R)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hsG₂
  obtain ⟨E, ⟨hE, hEa⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj hG₁ hsG₂ ha hBG₂
  haveI := hE
  refine ⟨E.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E).comp hG₂).congr (Category.id_comp _) rfl, ?_⟩
  rw [← Category.assoc, hEa, hi₂]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGenericExt

theorem symm_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (jK R))).pull (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L := by
  intro R _ _ _ _ _ G _ hG L hL h
  have e := GlobalTheory.SymBaseChange.inv_left_fst _ _ G (jK R)
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R))
    (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom (jK R)) e
  refine GlobalTheory.GenericDec.lbIso_of_generic G hG (pull_isLB hL _) hL ?_
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h2)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h1 h)

end GlobalTheory.SymGenericExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.eighthPower_formBundle_matrices_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  first | exact @GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint | exact GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint | (intros; apply GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint <;> assumption)
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

theorem _root_.GlobalTheory.T.iso_abelianScheme_semiAbelian_of_common_genericFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] (A G : Over (Sp O)) [GrpObj A] [GrpObj G] [IsCommMonObj G], IsAbelianScheme A → IsSemiAbelian G → ∀ (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (B : Over (Sp K)) [GrpObj B] (a : B.left ⟶ A.left) (g : B.left ⟶ G.left), IsGrpPullback B A (spMap (algebraMap O K)) a → IsGrpPullback B G (spMap (algebraMap O K)) g → ∃ i : A ≅ G, IsMonHom i.hom ∧ a ≫ i.hom.left = g ∧ (∀ (L : LB A.left) (L' : LB G.left), L.IsLB → L'.IsLB → LBIso (L.pull a) (L'.pull g) → LBIso L (L'.pull i.hom.left)) ∧ ∀ (e : A ⟶ A) (f : G ⟶ G) (eB : B ⟶ B), eB.left ≫ a = a ≫ e.left → eB.left ≫ g = g ≫ f.left → e ≫ i.hom = i.hom ≫ f := by
  first | exact @GlobalTheory.UPoinc.iso_of_common_generic_fibre | exact GlobalTheory.UPoinc.iso_of_common_generic_fibre | (intros; apply GlobalTheory.UPoinc.iso_of_common_generic_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (B B' : Over (Sp Ω)) [GrpObj B] [GrpObj B'] (b : B.left ⟶ A.left) (b' : B'.left ⟶ A'.left), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback B A (spMap j) b → IsGrpPullback B' A' (spMap j) b' → ∀ f : B ⟶ B', IsMonHom f → ∃ f₀ : A ⟶ A', IsMonHom f₀ ∧ b ≫ f₀.left = f.left ≫ b' := by
  first | exact @GlobalTheory.AlgClosedHomDescent.hom_descends | exact GlobalTheory.AlgClosedHomDescent.hom_descends | (intros; apply GlobalTheory.AlgClosedHomDescent.hom_descends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.abelian_of_fieldExtension_pullback_proper : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Sp K)) [GrpObj G] (B : Over (Sp K')) [GrpObj B] (φ : B.left ⟶ G.left) (g : ℕ), IsSemiAbelian G → IsGrpPullback B G (spMap i) φ → IsProper B.hom → SmoothOfRelativeDimension g B.hom → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.Mum.GenDesc.abelian_of_field_of_pullback | exact GlobalTheory.Mum.GenDesc.abelian_of_field_of_pullback | (intros; apply GlobalTheory.Mum.GenDesc.abelian_of_field_of_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_matrixUnits_extend_normal_noetherian : ∀ {S B : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U₀ : S.Opens) (hU : Dense (U₀ : Set S)) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (G' : Over U₀.toScheme) [GrpObj G'] (P : Over B) [GrpObj P] [IsCommMonObj P] (f : U₀.toScheme ⟶ B) (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G U₀.ι φ) (hψ : IsGrpPullback G' P f ψ) (E' : Fin 8 → Fin 8 → (P ⟶ P)) (hE' : ∀ a b, IsMonHom (E' a b)) (hrel : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1) (hsum : ∏ a, E' a a = 𝟙 P), ∃ E : Fin 8 → Fin 8 → (G ⟶ G), (∀ a b, IsMonHom (E a b)) ∧ (∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) ∧ ∏ a, E a a = 𝟙 G ∧ ∀ a b, ∃ e : G' ⟶ G', IsMonHom e ∧ e.left ≫ φ = φ ≫ (E a b).left ∧ e.left ≫ ψ = ψ ≫ (E' a b).left := by
  first | exact @GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend | exact GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend | (intros; apply GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.semiAbelian_pullback_abelian_over_open : ∀ {S X : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hX : IsSeparated (toZ X)) (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (H : Over S) [GrpObj H] (hH : IsSemiAbelian H) (U₀ U : S.Opens) (hU₀ : (U₀ : Set S).Nonempty) (hU : (U : Set S).Nonempty) (u' : U₀.toScheme ⟶ X) (c : U.toScheme ⟶ X) (A₀ : Over U₀.toScheme) [GrpObj A₀] (e₀ : A₀.left ⟶ H.left) (e₁ : A₀.left ⟶ A.left) (h₀ : IsGrpPullback A₀ H U₀.ι e₀) (h₁ : IsGrpPullback A₀ A u' e₁) (K : Type) [Field K] (pt : Sp K ⟶ S) (hpt : Set.range pt = {genericPoint S}) (hgen : ∀ (x : Sp K ⟶ U.toScheme) (y : Sp K ⟶ U₀.toScheme), x ≫ U.ι = pt → y ≫ U₀.ι = pt → x ≫ c = y ≫ u'), ∃ e : pullback A.hom c ⟶ H.left, IsGrpPullback ((Over.pullback c).obj A) H U.ι e := by
  first | exact @GlobalTheory.FactorOverOpen.factor_over_open | exact GlobalTheory.FactorOverOpen.factor_over_open | (intros; apply GlobalTheory.FactorOverOpen.factor_over_open <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isSemiAbelian_of_isGrpPullback_divisor : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → IsSemiAbelian G → IsSemiAbelian G' := by
  first | exact @GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | exact GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | (intros; apply GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusExtension_geometricFibres_of_descended_group : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  first | exact @GlobalTheory.Mum.torusExtension_of_descended | exact GlobalTheory.Mum.torusExtension_of_descended | (intros; apply GlobalTheory.Mum.torusExtension_of_descended <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAmpleXF

theorem relAmple_XF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)) :
    SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  intro mF
  have hP : IsProper tF.G.hom := MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper
  obtain ⟨w, hw, -⟩ := mF.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ tF.G tF.PP.L tF.PP.isLB inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.X) (U := ⊤)
    (x := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) s) trivial
  let f := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let U := f ⁻¹ᵁ V
  refine ⟨U, hs, ?_⟩
  have H : IsPullback ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (tF.G.hom ∣_ U) Xo.univ.t.G.hom (U.ι ≫ f) :=
    (isPullback_morphismRestrict tF.G.hom U).flip.paste_horiz mF.cart.1
  obtain ⟨w', hw'⟩ : LBIso (tF.PP.L.pull (tF.G.hom ⁻¹ᵁ U).ι) (Xo.univ.t.PP.L.pull ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ)) :=
    LBIso.chartPull (chartPullPull _ _)
      (chartPullSame Xo.univ.t.PP.L (fun _ : PUnit => (tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (fun _ => mF.φ) (fun _ => 1)
        (tF.G.hom ⁻¹ᵁ U).ι fun _ => rfl) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (tF.G.hom ∣_ U)) H Xo.univ.t.PP.isLB (pull_isLB tF.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) Xo.univ.ample

end GlobalTheory.PullAmpleXF
end
