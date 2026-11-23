module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsMultiplicativeGroup
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  first | exact @GlobalTheory.MumLin.exists_linearisation | exact GlobalTheory.MumLin.exists_linearisation | (intros; apply GlobalTheory.MumLin.exists_linearisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_spread_polarisedAbelianVariety_finitely_many_points : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (I : Type) [Finite I] (y : I → (baseOver (Sp Ω) ⟶ A.A)), ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra F T) (jT : T →+* Ω) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left) (y₀ : I → (baseOver (Sp T) ⟶ P.A)), Algebra.FiniteType F T ∧ Function.Injective jT ∧ jT.comp (algebraMap F T) = em ∧ IsGrpPullback A.A P.A (spMap jT) φ ∧ LBIso A.L (P.L.pull φ) ∧ ∀ i, (y i).left ≫ φ = spMap jT ≫ (y₀ i).left := by
  first | exact @GlobalTheory.SpreadPolAV.exists_spread | exact GlobalTheory.SpreadPolAV.exists_spread | (intros; apply GlobalTheory.SpreadPolAV.exists_spread <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isThetaPt_fibre_spread_model_at_fieldPoint : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (m : ℕ) (I : Type) (x : I → (baseOver (Sp Ω) ⟶ A.A)) (y : I → (baseOver (Sp T) ⟶ P.A)) (v : I → F), Odd m → 3 ≤ m → (∀ i, (x i).left ≫ φ = spMap jT ≫ (y i).left) → (∀ i, y i ^ (m ^ 2) = 1) → (∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ m = 1 → ∃ i, ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) ^ m = z) → IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → IsThetaPt P m (fun i => (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v i)) := by
  first | exact @GlobalTheory.Mum.isThetaPt_fibre | exact GlobalTheory.Mum.isThetaPt_fibre | (intros; apply GlobalTheory.Mum.isThetaPt_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.pow_eq_one_of_isGrpPullback_of_injective_domain : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → ∀ (x : baseOver (Sp Ω) ⟶ A.A) (y : baseOver (Sp T) ⟶ P.A) (k : ℕ), x.left ≫ φ = spMap jT ≫ y.left → x ^ k = 1 → y ^ k = 1 := by
  first | exact @GlobalTheory.Mum.pow_eq_one_of_isGrpPullback_of_injective | exact GlobalTheory.Mum.pow_eq_one_of_isGrpPullback_of_injective | (intros; apply GlobalTheory.Mum.pow_eq_one_of_isGrpPullback_of_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisation_ringAction_adjoint_cubeBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  first | exact @GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star | exact GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star | (intros; apply GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisation_bundle_genericFibre_descent : ∀ (R W R₂ W₂ K' Ω' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] [Field K'] [Field Ω'] (φ : R →+* W) (ρ : R →+* R₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (io : FractionRing R →+* K') (j : FractionRing W →+* Ω') (l : K' →+* Ω') (i : K' ≃+* FractionRing R₂) (j₂ : FractionRing W₂ →+* Ω'), Function.Injective φ → Function.Injective ρ → Function.Injective σ → Function.Injective φ₂ → φ₂.comp ρ = σ.comp φ → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) → (∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r))) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (α : AW.A.left ⟶ A.A.left), IsGrpPullback GW G (spMap φ) βW → UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (p : pullback AW.A.hom (spMap j) ⟶ A₁.A.left), IsGrpPullback A₁.A A.A (spMap io) α₁ → p ≫ α₁ = pullback.fst _ _ ≫ α → p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l → LBIso (AW.L.pull (pullback.fst AW.A.hom (spMap j))) (A₁.L.pull p) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsGrpPullback G₂ G (spMap ρ) β → IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q → LBIso A₂.L (A₁.L.pull q) → gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (GW' : Over (Sp W₂)) [GrpObj GW'] [IsCommMonObj GW'] (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' → IsGrpPullback GW' GW (spMap σ) τ → βW' ≫ β = τ ≫ βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.unif_bundle_generic_descent | exact GlobalTheory.unif_bundle_generic_descent | (intros; apply GlobalTheory.unif_bundle_generic_descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.exists_polarization_sectionBasis_pullback_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (f : R →+* R') (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap f) ψ → LBIso P'.L (P.L.pull ψ) → ∀ th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R))), IsSecBasis _ (fun _ : Fin 1 => th) → ∃ th' : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp R'))), IsSecBasis _ (fun _ : Fin 1 => th') := by
  first | exact @GlobalTheory.SecBasisPull.exists_secBasis_pull | exact GlobalTheory.SecBasisPull.exists_secBasis_pull | (intros; apply GlobalTheory.SecBasisPull.exists_secBasis_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagSqAxes

theorem lift_mul_lift₂ {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem weilIs_one_of_gen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) {N : ℕ} {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) : Out.WeilIs A L N x y 1 := by
  have hG := GlobalTheory.globalFns_holds
  have hM : (GlobalTheory.UU.trivRig A).L.IsLB := Out.Inh.trivLB_isLB _
  have h1 : Out.WeilIs A (GlobalTheory.UU.trivRig A).L N (x ≫ 𝟙 A) (y ≫ 𝟙 A) 1 := by
    rw [Category.comp_id, Category.comp_id]
    exact (GlobalTheory.UU.cubWeil_iff_weilIs (c := GlobalTheory.UU.trivCub A) hG hA hx hy 1).1 (GlobalTheory.UU.cubWeil_triv hx hy)
  have hw : LBIso (lbPow L 1) ((GlobalTheory.UU.trivRig A).L.pull (Over.Hom.left (𝟙 A))) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hL 1) hL (pull_isLB hM _) (GlobalTheory.lbIso_lbPow_one hL)
      (GlobalTheory.ZH.AbelianFibre.lbIso_of_gens t ht (GlobalTheory.UU.unitGen _ _) (GlobalTheory.UU.unitGen_isGen _ _))
  have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hM (𝟙 A) hw h1
  simp only [Nat.cast_one, _root_.mul_one] at h2
  exact h2

theorem weilIs_axis {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB B.left} (hP : P.IsLB) (ψ : A ⟶ B) [IsMonHom ψ]
    (ht : ∃ t : (P.pull ψ.left).Gen, t.IsGen) (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ)
    (hN : 0 < N) (hNk : (N : κ) ≠ 0) (a b : Over.mk y ⟶ A) (ha : a ^ N = 1) (hb : b ^ N = 1) :
    Out.WeilIs B P N (a ≫ ψ) (b ≫ ψ) 1 := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := ht
  have hL : (P.pull ψ.left).IsLB := pull_isLB hP _
  have pa : (a ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, ha, MonObj.one_comp]
  have pb : (b ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hb, MonObj.one_comp]
  obtain ⟨c', hc'⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S B P hB hP κ y N hN hNk _ _ pa pb
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hP ψ (GlobalTheory.lbIso_lbPow_one hL) hc'
  simp only [Nat.cast_one, _root_.mul_one] at h1
  have h2 := weilIs_one_of_gen hA hL t ht ha hb
  rwa [GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h1 h2] at hc'

end GlobalTheory.DiagSqAxes

namespace GlobalTheory.DiagSqAxes

theorem weilIs_diag_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ), 0 < N → (N : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ N = 1 → b ^ N = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P N (lift a 1) (lift 1 b) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N a b (c ^ 2) := by
  intro S A _ _ hA P hP h₂ h₁ hsym κ _ _ y N hN hNk a b ha hb c hc
  have hG := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have e11 : Out.WeilIs (G2 A) P N (lift a 1) (lift b 1) 1 := by
    have h := weilIs_axis hA hAA hP (lift (𝟙 A) (1 : A ⟶ A)) h₁ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e22 : Out.WeilIs (G2 A) P N (lift 1 a) (lift 1 b) 1 := by
    have h := weilIs_axis hA hAA hP (lift (1 : A ⟶ A) (𝟙 A)) h₂ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e21 : Out.WeilIs (G2 A) P N (lift 1 a) (lift b 1) c := by
    have hw : LBIso (lbPow P 1) (P.pull (lift (snd A A) (fst A A)).left) :=
      LBIso.trans (GlobalTheory.isLB_lbPow hP 1) hP (pull_isLB hP _) (GlobalTheory.lbIso_lbPow_one hP) hsym
    have h' : Out.WeilIs (G2 A) P N (lift 1 a ≫ lift (snd A A) (fst A A)) (lift b 1 ≫ lift (snd A A) (fst A A)) c := by
      simpa only [comp_lift, lift_fst, lift_snd] using hc
    have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP _ hw h'
    simp only [Nat.cast_one, _root_.mul_one] at h
    exact h
  have r1 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP e11 e21
  have r2 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc e22
  rw [lift_mul_lift₂] at r1 r2
  have s := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP (GlobalTheory.CommPairing.weilIs_symm hP r1)
    (GlobalTheory.CommPairing.weilIs_symm hP r2)
  have s' := GlobalTheory.CommPairing.weilIs_symm hP s
  rw [lift_mul_lift₂] at s'
  simp only [_root_.mul_one, _root_.one_mul] at s'
  have hd : Out.WeilIs (G2 A) P N (a ≫ lift (𝟙 A) (𝟙 A)) (b ≫ lift (𝟙 A) (𝟙 A)) (c ^ 2) := by
    simp only [comp_lift, Category.comp_id]
    convert s' using 1
    rw [← _root_.mul_inv, inv_inv, pow_two]
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hD hP (lift (𝟙 A) (𝟙 A)) (GlobalTheory.lbIso_lbPow_one hD) hd
  simp only [Nat.cast_one, _root_.mul_one] at h
  exact h

end GlobalTheory.DiagSqAxes
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_polAV_common_pullback : ∀ (Ω : Type) [Field Ω] (T T' : Scheme.{0}) (Q : PolAV T) (P' : PolAV T') (f : Sp Ω ⟶ T) (f' : Sp Ω ⟶ T') (G' : Over (Sp Ω)) [GrpObj G'] (a₁ : G'.left ⟶ Q.A.left) (a₂ : G'.left ⟶ P'.A.left), IsGrpPullback G' Q.A f a₁ → IsGrpPullback G' P'.A f' a₂ → LBIso (Q.L.pull a₁) (P'.L.pull a₂) → ∃ (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ Q.A.left) (a' : P₀.A.left ⟶ P'.A.left) (e : G'.left ⟶ P₀.A.left), IsIso e ∧ e ≫ a = a₁ ∧ e ≫ a' = a₂ ∧ IsGrpPullback P₀.A Q.A f a ∧ IsGrpPullback P₀.A P'.A f' a' ∧ LBIso P₀.L (Q.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro Ω _ T T' Q P' f f' G' _ a₁ a₂ h₁ h₂ hL
  obtain ⟨P₀, φ, hφ, hL₀⟩ := exists_pol_baseChange Q f
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ hφ
  haveI := he
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hφ' : φ = e.inv.left ≫ a₁ := by
    rw [← hea, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hiso : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  refine ⟨P₀, φ, e.inv.left ≫ a₂, e.hom.left, hiso, hea, ?_, hφ, ?_, hL₀, ?_⟩
  · rw [← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.id_comp]
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · exact LBIso.trans P₀.isLB (pull_isLB Q.isLB _) (pull_isLB P'.isLB _) hL₀
      (GenSpread.lbIso_pull_comp e.inv.left hφ' rfl hL)

end GlobalTheory.UPoinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  first | exact @GlobalTheory.KTrivSqZero.kTriv_lift | exact GlobalTheory.KTrivSqZero.kTriv_lift | (intros; apply GlobalTheory.KTrivSqZero.kTriv_lift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.symmetric_of_lineBundleIso_pull_groupHom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f → ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  first | exact @GlobalTheory.sym_of_lbIso_pull_hom | exact GlobalTheory.sym_of_lbIso_pull_hom | (intros; apply GlobalTheory.sym_of_lbIso_pull_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.abelianVariety_ampleBundles_descend_fg_subfield : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (k₀ : IntermediateField ℚ K) (A₀ : Over (Sp k₀)) (_ : GrpObj A₀) (π : A.left ⟶ A₀.left) (L₀ M₀ : LB A₀.left), k₀.FG ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap (algebraMap k₀ K)) π ∧ L₀.IsLB ∧ M₀.IsLB ∧ RelAmple A₀ L₀ ∧ RelAmple A₀ M₀ ∧ LBIso (L₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) L₀ ∧ LBIso (M₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) M₀ ∧ LBIso L (L₀.pull π) ∧ LBIso M (M₀.pull π) := by
  first | exact @GlobalTheory.AbFGSpread.spread_to_fg_subfield | exact GlobalTheory.AbFGSpread.spread_to_fg_subfield | (intros; apply GlobalTheory.AbFGSpread.spread_to_fg_subfield <;> assumption)
end
