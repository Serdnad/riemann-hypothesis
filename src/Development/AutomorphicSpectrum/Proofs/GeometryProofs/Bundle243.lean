module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle241
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsTorsionGroupExtension
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle054
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NatCastSmulMemHtLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle242
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_torsion_quasi_finite_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (n : ℕ), IsSemiAbelian G → 0 < n → FullTorsion G (spMap (algebraMap R (FractionRing R)) ≫ x) n → ∃ (T : Type) (_ : CommGroup T) (_ : Finite T) (Q : BT.QFGroup R T) (i : Q.G.left ⟶ G.left), Q.IsTorsionAlong G x n i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup | exact GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup | (intros; apply GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem exists_qfGroup_of_generic_fullTorsion : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [CharZero R'] (Ω : Type) [Field Ω] [Algebra R' Ω] [IsFractionRing R' Ω] (T : Type) [CommGroup T] (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (x' : Spec (CommRingCat.of R') ⟶ X) (ξ : Spec (CommRingCat.of Ω) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap R' Ω)) ≫ x' = ξ → ∀ N : ℕ, 1 ≤ N → ∀ pt : T →* (Over.mk ξ ⟶ G), Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → FullTorsion G ξ N → ∃ (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G x' N i' ∧ ∀ (a : FractionRing R' →+* Ω), a.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω → ∀ t, (pt t).left = Spec.map (CommRingCat.ofHom a) ≫ (Γ'.pt t).left ≫ i' :=
  @PositivityTheory.Xgn.exists_torsion_group_extension

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.torsion_group_endomorphism_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.torsion_group_etale_of_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | exact GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.torsion_group_finite_of_proper : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TopPt

section Alg

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {r : ℕ}

theorem hom_eq_sum {O : Type} [CommRing O] (δ : X →+ O) :
    δ = ∑ i, δ (Module.Free.chooseBasis ℤ X i) •
      (Int.castAddHom O).comp ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
  ext x

  conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
  simp only [map_zsmul]
  simp [AddMonoidHom.finsetSum_apply, mul_comm]

theorem exists_dual (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) (a : Fin r) :
    ∃ x : X, ∀ φ : X →+ ℤ, φ x = bs.repr φ a := by
  refine ⟨∑ i, bs.repr ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom a • Module.Free.chooseBasis ℤ X i,
    fun φ => ?_⟩
  have e : φ = ∑ i, φ (Module.Free.chooseBasis ℤ X i) •
      ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
    ext x

    conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
    simp only [map_zsmul]
    simp [AddMonoidHom.finsetSum_apply, mul_comm]
  conv_rhs => rw [e]

  simp [map_sum, mul_comm]

theorem indep {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    LinearIndependent O (fun a => (Int.castAddHom O).comp (bs a)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  obtain ⟨x, hx⟩ := exists_dual bs a
  have := DFunLike.congr_fun hg x
  simpa [AddMonoidHom.finsetSum_apply, hx, Finsupp.single_apply] using this

theorem span_top {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) = ⊤ := by
  have key : ∀ φ : X →+ ℤ, (Int.castAddHom O).comp φ ∈
      Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) := by
    intro φ
    have e : (Int.castAddHom O).comp φ = ∑ a, ((bs.repr φ a : ℤ) : O) • (Int.castAddHom O).comp (bs a) := by
      ext x
      have e₀ := DFunLike.congr_fun (bs.sum_repr φ) x
      rw [AddMonoidHom.finsetSum_apply] at e₀

      rw [AddMonoidHom.comp_apply, ← e₀, map_sum]
      simp [AddMonoidHom.finsetSum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  rw [eq_top_iff]
  intro δ _
  rw [hom_eq_sum δ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (key _)

theorem image_basis {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ))
    (io : (X →+ O) →ₗ[O] V) (h : Function.Injective io) :
    LinearIndependent O (fun a => io ((Int.castAddHom O).comp (bs a))) ∧
      LinearMap.range io = Submodule.span O (Set.range fun a => io ((Int.castAddHom O).comp (bs a))) := by
  have hk : LinearMap.ker io = ⊥ := LinearMap.ker_eq_bot_of_injective h
  have hi := (indep (O := O) bs).map' io hk
  refine ⟨hi, ?_⟩
  rw [LinearMap.range_eq_map, ← span_top (O := O) bs, Submodule.map_span, ← Set.range_comp]
  rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem cast_comp {O K : Type} [CommRing O] [CommRing K] (c : O →+* K) (φ : X →+ ℤ) :
    c.toAddMonoidHom.comp ((Int.castAddHom O).comp φ) = (Int.castAddHom K).comp φ := by
  ext x; simp

end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem exists_pull {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (z : S' ⟶ S) :
    ∃ (G₀ : Over S') (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left), IsSemiAbelian G₀ ∧ IsGrpPullback G₀ G z ψ :=
  ⟨(Over.pullback z).obj G, inferInstance, pullback.fst G.hom z, IsSemiAbelian.pullback z G hG,
    isGrpPullback_pullback G z⟩

theorem lifts_iff {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') {X : Scheme.{0}} {z : Sp R ⟶ X} {G : Over X}
    [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (hp : IsGrpPullback G₀ G z ψ)
    {GK : Over (Sp R')} {φ₀ : GK.left ⟶ G₀.left} (hw : φ₀ ≫ G₀.hom = GK.hom ≫ spMap c)
    {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G z V) (M₀ : LieModel G₀ (𝟙 _) V)
    (hM₀ : ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) (e : V) (v : epsAt (𝟙 (Sp R')) ⟶ GK) :
    (v.left ≫ φ₀ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M₀.pt e).left) ↔ (v.left ≫ (φ₀ ≫ ψ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  constructor
  · intro h
    rw [← Category.assoc, h, Category.assoc, hM₀]
  · intro h
    apply hp.1.hom_ext
    · rw [Category.assoc, h, Category.assoc, hM₀]
    · have w₂ := Over.w (M₀.pt e)
      have w₃ := Over.w v
      rw [Category.assoc, hw, ← Category.assoc, w₃, Category.assoc, w₂]
      show (Spec.map _ ≫ 𝟙 _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem main : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) (G' : Over (Sp (𝓞 L))) [GrpObj G'] (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → IsGrpPullback τ.B G' (spMap (algebraMap (𝓞 L) L)) φ' → ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (V V' : Type) [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup V'] [Module (𝓞 L) V'] (M : LieModel G z V) (M' : LieModel G' (𝟙 _) V') (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∃ (ε : Fin r → V) (f : V →ₗ[𝓞 L] V'), (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt (ε a)).left)) ∧ (∀ (e : V) (v : epsAt (𝟙 (Sp L)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M'.pt (f e)).left)) ∧ LinearIndependent (𝓞 L) ε ∧ LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε) ∧ ∀ e' : V', ∃ (a : 𝓞 L) (e : V), a ≠ 0 ∧ f e = a • e' := by
  intro X G _ _ hG L _ _ z GK _ φ τ G' _ φ'
  let _ := τ.addCommGroup
  let _ := τ.grpB
  have := τ.free
  have := τ.finite
  intro hG' hφ hφ' MT hMT V V' _ _ _ _ M M' r bs
  obtain ⟨G₀, _, ψ, hG₀, hp⟩ := exists_pull G hG z
  obtain ⟨φO, hF, hw⟩ : ∃ φO : GK.left ⟶ G₀.left, φO ≫ ψ = φ ∧
      φO ≫ G₀.hom = GK.hom ≫ spMap (algebraMap (𝓞 L) L) :=
    ⟨hp.1.lift φ (GK.hom ≫ spMap (algebraMap (𝓞 L) L)) (by rw [hφ.1.w, Category.assoc]), hp.1.lift_fst _ _ _,
      hp.1.lift_snd _ _ _⟩
  subst hF
  have hO : IsGrpPullback GK G₀ (spMap (algebraMap (𝓞 L) L)) φO := hp.cancel hφ hw
  obtain ⟨M₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main (𝓞 L) X z G G₀ ψ V hp).1 M
  have hiff := lifts_iff (algebraMap (𝓞 L) L) hp hw M M₀ hM₀
  obtain ⟨io, f, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.torus_extension_lie_lattice (𝓞 L) L G₀ G' GK τ φO φ'
    hG₀ hG' hO hφ' MT hMT V V' M₀ M'
  obtain ⟨b1, b2⟩ := image_basis bs io h3
  refine ⟨fun a => io ((Int.castAddHom (𝓞 L)).comp (bs a)), f, fun a => ?_, fun e v h => h2 e v ((hiff e v).2 h),
    b1, h4.trans b2, h5⟩
  have := h1 ((Int.castAddHom (𝓞 L)).comp (bs a))
  rw [cast_comp] at this
  exact (hiff _ _).1 this

end GlobalTheory.CompanionTheory.Ar.TopPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_tate_weil_unique : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (y : Over.mk ξ ⟶ G) (q : Cpt ξ) (w w' : Module.Dual Ω E), y ^ n = 1 → M.IsHTAt L n y q w → (M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtUniq.isHTAt_iff | exact GlobalTheory.CompanionTheory.Ar.HtUniq.isHTAt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.HtUniq.isHTAt_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.curve_family_formal_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  first | exact @PositivityTheory.HtPt.Cf.family_ex | exact PositivityTheory.HtPt.Cf.family_ex
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.fibre_power_free_conj_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p := by
  first | exact @PositivityTheory.HtPt.Cf.fib_inj | exact PositivityTheory.HtPt.Cf.fib_inj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem _root_.GlobalTheory.T.glued_lattice_from_local_matrices : ∀ (L : Type) [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (n : ℕ) (g : Fin n → V) (F : Submodule (𝓞 L) V) (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) L), LinearIndependent L g → (∀ v, (T v).det ≠ 0) → C.det ≠ 0 → {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite → (∀ x, x ∈ F ↔ x ∈ Submodule.span L (Set.range g) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • g j)) → logIdx F (fun k => ∑ j, C j k • g j) = (∑ᶠ v : FinitePlace L, Real.log (v (T v).det)) + ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.logIdx_localFrames | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.logIdx_localFrames | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.logIdx_localFrames <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie

theorem isHTAt_iff (h455 : type_of% @GlobalTheory.T.lie_model_finite_base_change) (h876 : type_of% @GlobalTheory.T.section_eq_zero_of_values)
    {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (L : LB G.left) {n : ℕ} (hn : n ≠ 0)
    (hfull : FullTorsion G ξ n) {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E)
    {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω)
    (hx : Spec.map (CommRingCat.ofHom (κ.toRingHom.comp (algebraMap R (FractionRing R)))) ≫ x = ξ)
    {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (htor : Γ.IsTorsionAlong G x n i)
    {L₀ : Type} [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E)
    (hj : ∀ v, (M.pt (j v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (κ.toRingHom.comp (algebraMap R (FractionRing R))))) ≫ (M₀.pt v).left)
    (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E)
    (hW : ∀ (t : T) (k : Type) [Field k] [IsAlgClosed k] (a : Ω →+* k) (xk gk : Over.mk (spMap a ≫ ξ) ⟶ G) (c : kˣ),
      xk.left = spMap a ≫ y.left → gk.left = spMap a ≫ ptG κ.toRingHom i t →
        (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = a (κ (algebraMap R _ (χ t : R)))))
    (hHT : Γ.IsHT i M₀ n χ w₀) (hwj : ∀ v, w (j v) = κ (algebraMap R _ (w₀ v)))
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a : R, κ (algebraMap R _ a) ∈ regAt ξ q)
    (w' : Module.Dual Ω E) : M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum R, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ (κ.toRingHom.comp (algebraMap R (FractionRing R)))
    (κ.injective.comp (IsFractionRing.injective R _)) x hx p q hp hsub
  obtain ⟨s, hs, hv⟩ := hHT
  have hcore := fun W f hval (e' : E) (v : epsAt (X.fromSpecStalk q.1) ⟶ G) (hv' : M.Extends q e' v) =>
    core_tan h455 M p.asIdeal.primeCompl Γ i x hzs (genMap ξ q) _ hg M₀ j hj n w₀ w hwj s hv W f hval e' v hv'.1 hv'.2
  obtain ⟨W₀, f₀, hW₀, hf₀⟩ := lift_sec G Γ x n i htor q.1 _ hzs s
  have hval₀ : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
      y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
        ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W₀, valAt (y ≫ i) W₀ h f₀ = valAt y ⊤ le_top s :=
    fun y b hb h => hf₀ y (Spec.map (CommRingCat.ofHom b)) (hb.trans (spec_comp _ _)) h
  have hlat := (lieLat_carrier X G Ω ξ E M q).1
  have hw : w ∈ M.omLat q := fun e' he' => by
    obtain ⟨v, hv'⟩ := (hlat e').1 he'
    obtain ⟨c, hc, -⟩ := hcore W₀ f₀ hval₀ e' v hv'
    exact ⟨c, hc.symm⟩
  have hn' : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  constructor
  · rintro ⟨-, W, f, hWm, hf, hd⟩
    have hsec : (i.app W).hom f - Γ.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s = 0 := by
      refine h876 R T Γ (i ⁻¹ᵁ W) _ fun t h => ?_
      rw [valAt_sub, sub_eq_zero]
      refine Eq.trans ?_ (valAt_res _ _ ⊤ le_top h le_top s).symm
      rw [hs t]
      refine (valAt_comp (Γ.pt t).left i W h f).symm.trans ?_
      let k := AlgebraicClosure Ω
      let a : Ω →+* k := algebraMap Ω k
      let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
      obtain ⟨g, hg1, hg2⟩ := tors_ex κ.toRingHom htor hx t
      let c : kˣ := Units.map ((a.comp κ.toRingHom).comp (algebraMap R (FractionRing R))).toMonoidHom (χ t)
      have e0 : (ψ ≫ g).left = spMap a ≫ ptG κ.toRingHom i t := by rw [← hg2]; rfl
      have e1 : (ψ ≫ g).left = Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i := by
        rw [e0, spec_comp, Category.assoc]
      have h1 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i) ⁻¹ᵁ W :=
        fun z _ => h (by trivial)
      have h2 := hf k a (ψ ≫ y) (ψ ≫ g) c (by rw [e1]; exact h1) rfl (by rw [← comp_pow', hg1, MonObj.comp_one])
        ((hW t k a (ψ ≫ y) (ψ ≫ g) c rfl e0).2 rfl)
      apply (a.comp κ.toRingHom).injective
      exact (valAt_spec (a.comp κ.toRingHom) _ W h h1 f).symm.trans ((valAt_congr e1 W _ h1 f).symm.trans h2)
    have hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
        y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
          ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W, valAt (y ≫ i) W h f = valAt y ⊤ le_top s := by
      intro B _ y _ _ h
      refine (valAt_comp y i W h f).trans ?_
      rw [sub_eq_zero.1 hsec]
      exact valAt_res y (i ⁻¹ᵁ W) ⊤ le_top h le_top s
    refine ⟨(n : Ω)⁻¹ • (w' - w), fun e' he' => ?_, ?_⟩
    · obtain ⟨v, hv'⟩ := (hlat e').1 he'
      have hm : ⊤ ≤ v.left ⁻¹ᵁ W := HtUniq.tan_le v hv'.1 hWm
      obtain ⟨c, hc, hr⟩ := hcore W f hval e' v hv'
      obtain ⟨r, hr⟩ := hr hm
      obtain ⟨r', hr', he⟩ := hd e' v hv' hm
      have : ((n : Ω)⁻¹ • (w' - w)) e' = r' - genMap ξ q r := by
        have he' : w' e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * r' := he
        have hc' : w e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * genMap ξ q r := by
          rw [hc, hr, map_add (f := _), map_mul, map_natCast]
          rfl
        rw [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hn', mul_sub, he', hc',
          add_sub_add_left_eq_sub]
      rw [this]
      exact sub_mem hr' ⟨r, rfl⟩
    · rw [← Nat.cast_smul_eq_nsmul Ω, smul_smul, mul_inv_cancel₀ hn', one_smul, add_sub_cancel]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨add_mem hw (nsmul_mem hu n), W₀, f₀, hW₀, ?_, ?_⟩
    · intro K _ _ a xk g' c h hxk hg' hweil
      obtain ⟨g₀, hg₀⟩ := hfull K a g' hg'
      have hg0 : g₀ ^ n = 1 := pow_descend a hg₀ hg'
      obtain ⟨t, ht⟩ := tors_pt κ.toRingHom htor hx g₀ hg0
      have hc₁ := (hW t K a xk g' c hxk (by rw [hg₀, ht])).1 hweil
      have e1 : g'.left = (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left) ≫ i := by
        rw [hg₀, ht, spec_comp]; simp only [ptG, Category.assoc]
      refine (valAt_congr e1 W₀ h (by rw [← e1]; exact h) f₀).trans ?_
      rw [hval₀ _ (a.comp (genMap ξ q)) (by
        rw [Category.assoc, Over.w, RingHom.comp_assoc, hg, ← RingHom.comp_assoc, spec_comp (algebraMap R _)]; rfl)]
      refine (valAt_spec (a.comp κ.toRingHom) (Γ.pt t).left ⊤ le_top le_top s).trans ?_
      rw [hs t, hc₁]
      rfl
    · intro e' v hv' h
      obtain ⟨c, hc', hr⟩ := hcore W₀ f₀ hval₀ e' v hv'
      obtain ⟨r, hr⟩ := hr h
      refine ⟨genMap ξ q r + u e', add_mem ⟨r, rfl⟩ (hu e' ((hlat e').2 ⟨v, hv'⟩)), ?_⟩
      rw [LinearMap.add_apply, LinearMap.smul_apply, hc', hr, map_add (f := _), map_mul, map_natCast, nsmul_eq_mul, mul_add,
        ← add_assoc]
      rfl

end GlobalTheory.CompanionTheory.HtLink
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.tate_iso_torsion_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (I : TateIso D (FractionRing O) (Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))), ∃ X : TorsTower p t.G y D.La, (∀ n (a : D.La), ((X.Γ n).pt (lev p n a)).left ≫ X.i n = (I.ev (p ^ n) a).left) ∧ ∀ a : 𝓞 E, X.Induces (t.act.act a) (DistribSMul.toAddMonoidHom D.La a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tower_exists | exact GlobalTheory.CompanionTheory.Ar.HT.tower_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tower_exists <;> assumption)
end
