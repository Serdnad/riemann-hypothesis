module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Mathlib.AlgebraicGeometry.ResidueField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.existsUnique_tangent_dual_number : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L), ∃! (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieModel_exists_unique_act : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E)
    (O : Type) [CommRing O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G →
    (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) →
    ∃! ρ : O →+* Module.End R E, M.IsActOf act ρ := by
  intro S G _ R _ x E _ _ M O _ act hmon h1 hmul hadd
  have hex : ∀ a, ∃ A : E →ₗ[R] E, (∀ e, M.pt (A e) = M.pt e ≫ act a) ∧
      ∀ B : E →ₗ[R] E, (∀ e, M.pt (B e) = M.pt e ≫ act a) → B = A := by
    intro a
    have := hmon a
    exact lieModel_exists_unique_diff S G G R x E E M M (act a)
  choose A hA hAu using hex
  have hone : LinearMap.id = A 1 := hAu 1 LinearMap.id fun e => by
    rw [h1, Category.comp_id]
    rfl
  have hmul' : ∀ a b, A (a * b) = A a * A b := fun a b => (hAu (a * b) (A a * A b) fun e => by
    rw [Module.End.mul_apply, hA a, hA b, Category.assoc, ← hmul b a, mul_comm]).symm
  have hadd' : ∀ a b, A (a + b) = A a + A b := fun a b => (hAu (a + b) (A a + A b) fun e => by
    rw [LinearMap.add_apply, M.add, hA a, hA b, ← MonObj.comp_mul, hadd]).symm
  refine ⟨RingHom.mk' { toFun := A, map_one' := hone.symm, map_mul' := hmul' } hadd',
    fun a e => hA a e, fun ρ hρ => ?_⟩
  ext a : 1
  exact hAu a (ρ a) (hρ a)

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_existsUnique_equiv : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G x E'), ∃! f : E ≃ₗ[R] E', ∀ e, M'.pt (f e) = M.pt e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv | exact GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_functorial_map : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G' x E') (f : G ⟶ G') [IsMonHom f], ∃! A : E →ₗ[R] E', ∀ e, M'.pt (A e) = M.pt e ≫ f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff | exact GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.isFinOpenSub_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | exact GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_lie_model : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S), ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E), Nonempty (LieModel G x E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_exists | exact GlobalTheory.CompanionTheory.Ar.lieModel_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_exists <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem regularAt_forall_iff_exists_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t :=
  PositivityTheory.HtPt.Unc.reg_iff

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem section_eq_zero_of_val_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 :=
  PositivityTheory.HtPt.Unc.sec_inj

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_eq_top_of_etale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), Etale Γ.G.hom → Γ.btOrder ⊤ = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale | exact GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem isDVR_of_ringKrullDim_eq_one (B : Type*) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (h : ringKrullDim B = 1) : IsDiscreteValuationRing B := by
  have hf : ¬ IsField B := fun hB => by
    rw [ringKrullDim_eq_zero_of_isField hB] at h
    exact zero_ne_one h
  have hle : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.2 (by rw [h]; rfl)
  have hmax := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hle
  have hT := (IsDiscreteValuationRing.TFAE B hf).out 1 4
  refine hT.2 ⟨inferInstance, ExistsUnique.intro (IsLocalRing.maximalIdeal B) ⟨?_, inferInstance⟩ ?_⟩
  · exact fun h0 => hf (IsLocalRing.isField_iff_maximalIdeal_eq.2 h0)
  · rintro Q ⟨h0, hQ⟩
    have := hmax Q h0 hQ
    exact IsLocalRing.eq_maximalIdeal this

theorem comap_maximalIdeal_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : PrimeSpectrum (X.presheaf.stalk y)) (hP : X.fromSpecStalk y P = x) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P.asIdeal := by
  have e := Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  have e3 : (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x)) = x := by
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have e2 : X.fromSpecStalk y (Spec.map (X.presheaf.stalkSpecializes h)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))) = X.fromSpecStalk y P :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (e3.trans hP.symm)
  have inj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  exact congrArg PrimeSpectrum.asIdeal (inj e2)

theorem exists_mul_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : Ideal (X.presheaf.stalk y))
    (hP : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P)
    (b : X.presheaf.stalk x) :
    ∃ a, a ∉ P ∧ ∃ c, (X.presheaf.stalkSpecializes h).hom a * b = (X.presheaf.stalkSpecializes h).hom c := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have loc := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl b
  have hg : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U y hyU).hom r) =
      algebraMap Γ(X, U) (X.presheaf.stalk x) r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU h) r
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (t : Γ(X, U))) := IsLocalization.map_units _ t
  refine ⟨(X.presheaf.germ U y hyU).hom t, fun hm => ?_, (X.presheaf.germ U y hyU).hom r, ?_⟩
  · rw [← hP, Ideal.mem_comap, hg] at hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  · rw [hg, hg, mul_comm]
    exact ht

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem exists_generisation_of_height_eq_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → IsLocallyNoetherian X → IsNormalScheme X → ∀ (p : Cpt ξ) (P : PrimeSpectrum (regAt ξ p)), P.asIdeal.height = 1 → ∃ (q : Cpt ξ) (hs : q.1 ⤳ p.1), (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) ∧ (∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q) ∧ ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p := by
  intro X Ω _ ξ hgen hN hnorm p P hP
  let P' : PrimeSpectrum (X.presheaf.stalk p.1) := ⟨Ideal.comap (regIso hgen p) P.asIdeal, inferInstance⟩
  have hP' : P'.asIdeal.height = 1 := ((regIso hgen p).height_comap P.asIdeal).trans hP
  have hmem : ∀ a, a ∈ P'.asIdeal ↔ regIso hgen p a ∈ P.asIdeal := fun a => Iff.rfl
  have hs : X.fromSpecStalk p.1 P' ⤳ p.1 := by
    have h : X.fromSpecStalk p.1 P' ∈ Set.range (X.fromSpecStalk p.1) := ⟨P', rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  have hgq : genPt ξ ⤳ X.fromSpecStalk p.1 P' := by
    have e1 : genPt ξ = X.fromSpecStalk p.1 (spMap (genMap ξ p)
        (IsLocalRing.closedPoint Ω : Sp Ω)) :=
      (congrArg (fun g : Sp Ω ⟶ X => g (IsLocalRing.closedPoint Ω : Sp Ω))
        (spMap_genMap_fromSpecStalk p)).symm.trans (Scheme.Hom.comp_apply _ _ _)
    refine (specializes_of_eq e1).trans (Specializes.map ?_ (X.fromSpecStalk p.1).continuous)
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have h0 : genMap ξ p a ∈ IsLocalRing.maximalIdeal Ω := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h0
    have : a = 0 := hgen.inj p (h0.trans (map_zero _).symm)
    rw [this]
    exact Ideal.zero_mem _
  let q : Cpt ξ := ⟨X.fromSpecStalk p.1 P', hgq⟩
  have hs' : q.1 ⤳ p.1 := hs
  obtain ⟨hdom, hic⟩ := hnorm q.1
  haveI := hN
  let f : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hs').hom
  have hcomap : (IsLocalRing.maximalIdeal (X.presheaf.stalk q.1)).comap f = P'.asIdeal :=
    comap_maximalIdeal_stalkSpecializes hs' P' rfl
  have hgf : ∀ a, genMap ξ q (f a) = genMap ξ p a := genMap_specializes hs'
  have hfinj : Function.Injective f := fun a b hab =>
    hgen.inj p (by rw [← hgf, ← hgf, hab])
  have hunit : ∀ a, a ∉ P'.asIdeal → IsUnit (f a) := fun a ha => by
    by_contra hu
    exact ha (hcomap ▸ (IsLocalRing.mem_maximalIdeal _).2 hu)
  have hfrac : ∀ b, ∃ a, a ∉ P'.asIdeal ∧ ∃ c, f a * b = f c :=
    exists_mul_stalkSpecializes hs' P'.asIdeal hcomap
  have hdim : ringKrullDim (X.presheaf.stalk q.1) = 1 := by
    letI : Algebra (X.presheaf.stalk p.1) (X.presheaf.stalk q.1) := f.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk q.1) P'.asIdeal :=
      { map_units := fun s => hunit s.1 s.2
        surj := fun b => by
          obtain ⟨a, ha, c, hc⟩ := hfrac b
          exact ⟨⟨c, ⟨a, ha⟩⟩, by rw [mul_comm]; exact hc⟩
        exists_of_eq := fun {a b} h => ⟨1, by rw [hfinj h]⟩ }
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P'.asIdeal (X.presheaf.stalk q.1), hP']
    rfl
  refine ⟨q, hs', ⟨hdom, isDVR_of_ringKrullDim_eq_one _ hdim⟩, fun s hsP => ?_, ?_⟩
  · have ha : (regIso hgen p).symm s ∉ P'.asIdeal := by
      rw [hmem, RingEquiv.apply_symm_apply]
      exact hsP
    obtain ⟨u, hu⟩ := (hunit _ ha).exists_right_inv
    refine ⟨u, ?_⟩
    refine eq_inv_of_mul_eq_one_right ?_
    have h1 := congrArg (genMap ξ q) hu
    rw [map_mul, map_one, hgf, genMap_regIso_symm] at h1
    exact h1
  · rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha, c, hc⟩ := hfrac b
    refine ⟨regIso hgen p a, fun h => ha ((hmem a).2 h), ⟨c, ?_⟩⟩
    have h1 := congrArg (genMap ξ q) hc
    rw [map_mul, hgf, hgf] at h1
    exact h1.symm

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.isCptGen_residue_field_generic : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X, (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | exact GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | (intros; apply GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.regAt_fraction_noetherian_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω ∧ (IsNoetherianRing (X.presheaf.stalk p.1) → IsNoetherianRing (regAt ξ p)) ∧ (IsIntegrallyClosed (X.presheaf.stalk p.1) → IsIntegrallyClosed (regAt ξ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | exact GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | (intros; apply GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring <;> assumption)
end
