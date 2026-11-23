module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3358
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3359
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.nadel_vanishing_pairs_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair := by
  first | exact @GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | exact GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | (intros; apply GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semiabelianModel_proper_over_thetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (_ : ZHOut X₁.ρ Y U₀ EE) (q : Y.Z ⟶ X₁.M.Z), X₁.S.Over₀ Y U₀ ∧ X₁.S.IsEE Y U₀ EE ∧ IsProper q ∧ Y.pt ≫ q = X₁.M.pt ∧ (∀ z₁ : X₁.M.Z, _root_.IsPreconnected (q.base ⁻¹' {z₁})) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ y : Sp (OO p) ⟶ Y.Z, y ≫ q = c.y := by
  first | exact @GlobalTheory.Poinc.exists_zhModel_proper_over_setup | exact GlobalTheory.Poinc.exists_zhModel_proper_over_setup | (intros; apply GlobalTheory.Poinc.exists_zhModel_proper_over_setup <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZConn

theorem preconnectedSpace_of_isLocalRing (Z : Scheme.{0}) [IsLocalRing Γ(Z, ⊤)] : PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, hes⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z s hs
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    rw [← hes, Z.basicOpen_of_isUnit hu]
    simp
  · left
    have h0 : e = 0 := by
      have : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he, sub_self]
      exact hu.mul_left_eq_zero.1 this
    rw [← hes, h0, Z.basicOpen_zero]
    simp

theorem exists_complete_flat (R : Type) [CommRing R] [IsNoetherianRing R] (P : PrimeSpectrum R) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A) (φ : R →+* A),
      IsAdicComplete (maximalIdeal A) A ∧ φ.Flat ∧ (maximalIdeal A).comap φ = P.asIdeal := by
  let L := Localization.AtPrime P.asIdeal
  have fg : (maximalIdeal L).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal L) L) := AdicCompletion.isLocalRing_of_fg fg
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal L) L) := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let ψ := algebraMap L (AdicCompletion (maximalIdeal L) L)
  haveI : IsLocalHom ψ := ((IsLocalRing.local_hom_tfae ψ).out 1 3).mpr hm.symm.le
  refine ⟨AdicCompletion (maximalIdeal L) L, inferInstance, inferInstance, hloc, ψ.comp (algebraMap R L), ?_, ?_, ?_⟩
  · rw [hm]; exact AdicCompletion.isAdicComplete_self _ fg
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap ψ]
    exact Localization.AtPrime.under_maximalIdeal

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsLocallyNoetherian Y → IsProper a →
    (∀ V : Y.Opens, Function.Bijective (a.app V).hom) → ∀ y : Y, _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y a hY ha hbij y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsNoetherianRing Γ(Y, U) := hY.component_noetherian ⟨U, hU⟩
  let e := hU.isoSpec
  let P : PrimeSpectrum Γ(Y, U) := e.hom ⟨y, hyU⟩
  obtain ⟨A, _, _, _, φ, hAc, hφ, hφP⟩ := exists_complete_flat Γ(Y, U) P
  let π : (a ⁻¹ᵁ U).toScheme ⟶ Sp Γ(Y, U) := (a ∣_ U) ≫ e.hom
  let g : Sp A ⟶ Sp Γ(Y, U) := Spec.map (CommRingCat.ofHom φ)
  haveI : Flat g := HasRingHomProperty.Spec_iff.2 hφ
  haveI : IsProper π := inferInstance
  have hres : Function.Bijective ((a ∣_ U).app ⊤).hom := by
    rw [morphismRestrict_app]
    have h1 := hbij ((Scheme.Opens.ι U) ''ᵁ ⊤)
    have h2 := ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage a U ⊤)).op)
    exact h2.comp h1
  have hπ : Function.Bijective π.appTop.hom := by
    change Function.Bijective ((a ∣_ U) ≫ e.hom).appTop.hom
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    haveI : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact hres.comp (ConcreteCategory.bijective_of_isIso _)
  have hp := GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions Γ(Y, U) _ _ _ π g (pullback.snd π g) (pullback.fst π g) inferInstance inferInstance hπ
    inferInstance (IsPullback.of_hasPullback π g).flip
  let Z : Scheme.{0} := pullback π g
  let ψ : A →+* Γ(Z, ⊤) :=
    ((pullback.snd π g).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Bijective ψ := (hp ⊤).comp (ConcreteCategory.bijective_of_isIso _)
  haveI : Nontrivial Γ(Z, ⊤) := hψ.1.nontrivial
  haveI : IsLocalHom ψ := IsLocalHom.of_surjective ψ hψ.2
  haveI : IsLocalRing Γ(Z, ⊤) := IsLocalRing.of_surjective ψ hψ.2
  haveI : PreconnectedSpace Z := preconnectedSpace_of_isLocalRing Z
  have hfib := GlobalTheory.T.isPreconnected_closedFibre_proper_completeLocalNoetherian A hAc Z (pullback.snd π g) inferInstance inferInstance
  have hg : g (closedPoint A) = P := PrimeSpectrum.ext hφP
  have einj : Function.Injective e.hom := e.hom.isOpenEmbedding.injective
  have key : {x : X | a x = y} = (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) '' {z | pullback.snd π g z = closedPoint A} := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ a ⁻¹ᵁ U := by
        show a x ∈ U
        rw [hx]; exact hyU
      let x' : (a ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
      have h1 : (a ∣_ U) x' = ⟨y, hyU⟩ := Subtype.ext ((morphismRestrict_base_coe a U x').trans hx)
      have h2 : π x' = g (closedPoint A) := by
        rw [hg]
        change ((a ∣_ U) ≫ e.hom) x' = P
        rw [Scheme.Hom.comp_apply, h1]
      obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback π g) x' (closedPoint A) h2
      refine ⟨z, hz2, ?_⟩
      rw [Scheme.Hom.comp_apply, hz1]
      rfl
    · rintro ⟨z, hz, rfl⟩
      have h3 : π (pullback.fst π g z) = g (pullback.snd π g z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [hz, hg] at h3
      have h4 : (a ∣_ U) (pullback.fst π g z) = ⟨y, hyU⟩ := einj (by
        rw [← Scheme.Hom.comp_apply]; exact h3)
      show a ((pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) z) = y
      rw [Scheme.Hom.comp_apply]
      change a (pullback.fst π g z).1 = y
      rw [← morphismRestrict_base_coe a U, h4]
  rw [key]
  exact hfib.image _ (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι).continuous.continuousOn

end GlobalTheory.ZConn
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | exact GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | (intros; apply GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.lineBundleIso_of_compatible_adic_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) → (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' → Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) → LBIso A A' := by
  first | exact @GlobalTheory.FormalAlg.lbIso_of_compatible_reductions | exact GlobalTheory.FormalAlg.lbIso_of_compatible_reductions | (intros; apply GlobalTheory.FormalAlg.lbIso_of_compatible_reductions <;> assumption)
end
