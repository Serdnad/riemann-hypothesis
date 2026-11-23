module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  first | exact @GlobalTheory.EndLattice.congMod_y_of_end | exact GlobalTheory.EndLattice.congMod_y_of_end | (intros; apply GlobalTheory.EndLattice.congMod_y_of_end <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), U.P = P ∧ U.gen = gen := by
  first | exact @GlobalTheory.Mum.exists_preU_even | exact GlobalTheory.Mum.exists_preU_even | (intros; apply GlobalTheory.Mum.exists_preU_even <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FieldTraitExt

theorem exists_normalization (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R)
    (K' : Type) [Field K'] (io : FractionRing R →+* K') (hio : io.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂)
      (e : R₂ →+* K'), FinExt ρ ∧ Function.Injective e ∧ (∀ r, e (ρ r) = io (algebraMap R _ r)) ∧
      ∀ y, i (e y) = algebraMap R₂ _ y := by
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hchar⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hio
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let R₂ := integralClosure R K'
  haveI hfin : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) K' R₂
  haveI : IsLocalRing R₂ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) R₂
  haveI : IsFractionRing R₂ K' := IsIntegralClosure.isFractionRing_of_finite_extension R (FractionRing R) K' R₂
  have hRK : Function.Injective (algebraMap R K') := io.injective.comp (IsFractionRing.injective R _)
  have hinj : Function.Injective (algebraMap R R₂) := fun x y h => hRK (congrArg Subtype.val h)
  haveI : IsNoetherianRing R₂ := IsNoetherianRing.of_finite R R₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, algebraMap R R₂,
    (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).toRingEquiv, algebraMap R₂ K',
    ⟨⟨inferInstance, inferInstance, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, hinj, RingHom.finite_algebraMap.2 hfin⟩,
    Subtype.val_injective, fun r => rfl, fun y => ?_⟩
  exact (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).commutes y

theorem exists_trait (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (φ : R →+* W)
    (hφ : IsLocalHom φ) (ρ : R →+* R₂) (hρ : ρ.Finite) (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω)
    (m : R₂ →+* Ω) (hm : Function.Injective m) (hc : ∀ r, m (ρ r) = j (algebraMap W _ (φ r))) :
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧
      ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = m r := by
  first
  | exact @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | (apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension ..)

end GlobalTheory.FieldTraitExt

namespace GlobalTheory.FieldTraitExt

theorem exists_finite_extension_of_trait : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  intro R W _ _ _ _ _ _ hR hW φ _ hφ K' Ω _ _ io j l hio hc
  obtain ⟨R₂, _, _, _, ρ, i, e, hfe, he, heρ, hie⟩ := exists_normalization R hR K' io hio
  obtain ⟨W₂, _, _, _, σ, φ₂, j₂, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, hj₁, hj₂⟩ :=
    exists_trait R R₂ W hW φ hφ ρ hfe.2.2 Ω j (l.comp e) (l.injective.comp he)
      (fun r => by rw [RingHom.comp_apply, heρ, hc])
  refine ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hfe, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, fun r => ?_, hj₁,
    fun r => ?_⟩
  · rw [← heρ, hie]
  · rw [hj₂, RingHom.comp_apply]
    congr 1
    rw [RingEquiv.eq_symm_apply, hie]

end GlobalTheory.FieldTraitExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_fractionRing_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [Algebra (FractionRing R) E], FiniteDimensional (FractionRing R) E → IsGalois (FractionRing R) E → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (t : E →+* FractionRing R'), FinExt ρ ∧ ∀ r : R, t (algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r)) = algebraMap R' (FractionRing R') (ρ r) := by
  intro R _ _ _ hR E _ _ hfd hgal
  letI := hfd
  letI := hgal
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E) hR
  letI : Algebra R E := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  set R₂ := integralClosure R E
  haveI : IsFractionRing R₂ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E
  let t : E ≃ₐ[R₂] FractionRing R₂ := IsLocalization.algEquiv (nonZeroDivisors R₂) E (FractionRing R₂)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R R₂, t.toRingEquiv.toRingHom, hfe, ?_⟩
  intro r
  have h1 : algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r) = algebraMap R₂ E (algebraMap R R₂ r) := rfl
  rw [h1]
  change t (algebraMap R₂ E _) = _
  rw [AlgEquiv.commutes]

end GlobalTheory.GalClosure
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_pullback_injective_local : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R (maximalIdeal R) → AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → Has D → Has D' := by
  first | exact @GlobalTheory.Mum.has_pull | exact GlobalTheory.Mum.has_pull | (intros; apply GlobalTheory.Mum.has_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lineBundleIso_genericFibre_descend_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G' → IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → ∀ (L' : LB G'.left), L'.IsLB → LBIso (L'.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) → ∀ P : GlobalTheory.UU.CP G, LBIso L' (P.L.L.pull β) → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  first | exact @GlobalTheory.Mum.lbIso_generic_descend | exact GlobalTheory.Mum.lbIso_generic_descend | (intros; apply GlobalTheory.Mum.lbIso_generic_descend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.preUniformisationData_isEvenCubicalOnClosedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P := by
  first | exact @GlobalTheory.Mum.PreEven.evenOn_preU | exact GlobalTheory.Mum.PreEven.evenOn_preU | (intros; apply GlobalTheory.Mum.PreEven.evenOn_preU <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_fieldPoint_polarised_fibre_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, IsProper (G.hom ∣_ W) → ∀ y : PrimeSpectrum R, y ∈ W → y.asIdeal ≠ ⊥ → ∃ (K₁ : Type) (_ : Field K₁) (z : Sp K₁ ⟶ Sp R), z (closedPoint K₁) = y ∧ IsProper (pullback.snd G.hom z) ∧ RelAmple ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) ∧ KTriv ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) := by
  first | exact @GlobalTheory.PolPoint.exists_field_point_polarised | exact GlobalTheory.PolPoint.exists_field_point_polarised | (intros; apply GlobalTheory.PolPoint.exists_field_point_polarised <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteEtale_local_ext_residueField_separable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (k' : Type) [Field k'] [Algebra (ResidueField R) k'] [Module.Finite (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : k' →+* ResidueField R'), FinExt ρ ∧ ρ.Etale ∧ σ.comp ((algebraMap (ResidueField R) k').comp (residue R)) = (residue R').comp ρ := by
  first | exact @GlobalTheory.Mum.exists_finExt_etale_of_isSeparable | exact GlobalTheory.Mum.exists_finExt_etale_of_isSeparable | (intros; apply GlobalTheory.Mum.exists_finExt_etale_of_isSeparable <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FinExtComp

theorem finExt_comp_isPullDeg : ∀ (R R₀ R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₀ : R →+* R₀) (ρ₁ : R₀ →+* R₁) (D : DegPre R) (D₀ : DegPre R₀) (D₁ : DegPre R₁), FinExt ρ₀ → FinExt ρ₁ → Nonempty (IsPullDeg ρ₀ D D₀) → Nonempty (IsPullDeg ρ₁ D₀ D₁) → FinExt (ρ₁.comp ρ₀) ∧ Nonempty (IsPullDeg (ρ₁.comp ρ₀) D D₁) := by
  intro R R₀ R₁ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ D D₀ D₁ h₀ h₁ ⟨p⟩ ⟨q⟩
  exact ⟨⟨h₁.1, h₁.2.1.comp h₀.2.1, h₁.2.2.comp h₀.2.2⟩,
    GlobalTheory.PullDegComp.nonempty_isPullDeg_comp h₀.2.1 h₁.2.1 p q⟩

end GlobalTheory.Mum.FinExtComp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt_trans : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → HasFin D' → HasFin D := by
  first | exact @GlobalTheory.Mum.hasFin_of_finExt | exact GlobalTheory.Mum.hasFin_of_finExt | (intros; apply GlobalTheory.Mum.hasFin_of_finExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | exact GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | (intros; apply GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed <;> assumption)
end
