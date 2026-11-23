module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolFieldDescent

theorem exists_polAV : ∀ (K K' : Type) [Field K] [Field K'] (ga : K →+* K') (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → Out.Sym G L → ∀ (A' : PolAV (Sp K')) (α : A'.A.left ⟶ G.left), IsGrpPullback A'.A G (spMap ga) α → LBIso A'.L (L.pull α) → ∃ (A : PolAV (Sp K)) (gen : G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) L := by
  intro K K' _ _ ga G _ _ L hL hS A' α hP hw
  letI : Algebra K K' := ga.toAlgebra
  have hP' : IsGrpPullback A'.A G (spMap (algebraMap K K')) α := hP
  have : Flat (spMap ga) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap ga) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K) (B := K')⟩
  have : QuasiCompact (spMap ga) := inferInstance
  have hAb : IsAbelianScheme G := PolFlatDescent.isAbelianScheme_of_pull hP A'.isAb
  have hdim : SmoothOfRelativeDimension A'.g G.hom :=
    CM.smoothOfRelativeDimension_of_fibre K K' ga G A'.A.left α A'.A.hom A'.g hAb hP.1 A'.smoothDim
  have hrig : Out.Rigidified G L := DVR.exists_gen_of_local L hL _ _
  have hamp : Out.RelAmple G L :=
    AmpleDescent.relAmple_of_faithfullyFlat K K' G A'.A α L A'.L hAb hP' hL A'.isLB hw A'.ample
  have hK : Out.KTriv G L := AmpleDescent.kTriv_of_pull hP hL A'.isLB hw A'.ktriv
  refine ⟨⟨G, hAb, A'.g, hdim, L, hL, hrig, hS, hamp, hK⟩, Iso.refl G, ?_, ?_⟩
  · show IsMonHom (𝟙 G); infer_instance
  · exact GlobalTheory.lbIso_pull_id hL

end GlobalTheory.PolFieldDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem rigidified_and_sym_of_field_extension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  intro K K' _ _ i A _ A' _ φ hA h L L' hL hL' hw hS
  refine ⟨?_, (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K K' i A A' φ L L' hA h hL hL' hw).2.1 hS⟩
  have : Subsingleton (𝟙_ (Over (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum K) (pull_isLB hL _)

end GlobalTheory.Mum.GenDesc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorOverOpen

theorem isNormalScheme_opens {S : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (V : S.Opens) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.toScheme := fun x => by
  obtain ⟨h₁, h₂⟩ := h x.1
  have e := (V.stalkIso x).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem isNoetherian_opens {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (V : S.Opens) :
    AlgebraicGeometry.IsNoetherian V.toScheme := by
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact (V : Set S))
  exact {}

theorem exists_isGrpPullback_cancel {S S' S'' : Scheme.{0}} {H : Over S} {G : Over S'} {A' : Over S''}
    [GrpObj H] [GrpObj G] [GrpObj A'] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : A'.left ⟶ H.left} {ψ : G.left ⟶ H.left}
    (hφ : IsGrpPullback A' H (g ≫ f) φ) (hψ : IsGrpPullback G H f ψ) :
    ∃ φ' : A'.left ⟶ G.left, IsGrpPullback A' G g φ' := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso hφ ((isGrpPullback_pullback G g).comp hψ)
  exact ⟨_, ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G g)).congr (Category.id_comp _) rfl⟩

end GlobalTheory.FactorOverOpen


open GlobalTheory.FactorOverOpen in
theorem GlobalTheory.FactorOverOpen.factor_over_open : ∀ {S X : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hX : IsSeparated (toZ X)) (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (H : Over S) [GrpObj H] (hH : IsSemiAbelian H) (U₀ U : S.Opens) (hU₀ : (U₀ : Set S).Nonempty) (hU : (U : Set S).Nonempty) (u' : U₀.toScheme ⟶ X) (c : U.toScheme ⟶ X) (A₀ : Over U₀.toScheme) [GrpObj A₀] (e₀ : A₀.left ⟶ H.left) (e₁ : A₀.left ⟶ A.left) (h₀ : IsGrpPullback A₀ H U₀.ι e₀) (h₁ : IsGrpPullback A₀ A u' e₁) (K : Type) [Field K] (pt : Sp K ⟶ S) (hpt : Set.range pt = {genericPoint S}) (hgen : ∀ (x : Sp K ⟶ U.toScheme) (y : Sp K ⟶ U₀.toScheme), x ≫ U.ι = pt → y ≫ U₀.ι = pt → x ≫ c = y ≫ u'), ∃ e : pullback A.hom c ⟶ H.left, IsGrpPullback ((Over.pullback c).obj A) H U.ι e := by
  intro S X _ _ hS hX A _ hA H _ hH U₀ U hU₀ hU u' c A₀ _ e₀ e₁ h₀ h₁ K _ pt hpt hgen

  let V : S.Opens := U ⊓ U₀
  have hη : ∀ W : S.Opens, (W : Set S).Nonempty → genericPoint S ∈ W := fun W hW =>
    ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 (by simpa using hW)
  have hηV : genericPoint S ∈ V := ⟨hη U hU, hη U₀ hU₀⟩
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty U := ⟨⟨_, hη U hU⟩⟩
  let jU : V.toScheme ⟶ U.toScheme := S.homOfLE inf_le_left
  let j₀ : V.toScheme ⟶ U₀.toScheme := S.homOfLE inf_le_right
  have hjU : jU ≫ U.ι = V.ι := S.homOfLE_ι _
  have hj₀ : j₀ ≫ U₀.ι = V.ι := S.homOfLE_ι _

  have hrange : Set.range pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hpt]
    simpa using hηV
  let z : Sp K ⟶ V.toScheme := IsOpenImmersion.lift V.ι pt hrange
  have hz : z ≫ V.ι = pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant z := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq,
      V.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, ← Set.range_comp]
    have : (⇑V.ι ∘ ⇑z) = ⇑pt := by rw [← hz]; rfl
    rw [this, hpt, (genericPoint_spec S).def]
    rfl
  have ha : jU ≫ c = j₀ ≫ u' := by
    refine ext_of_isDominant_of_isSeparated (ReciprocityTheory.ChartRestriction.G.Semi.toZ X)
      (specULiftZIsTerminal.hom_ext _ _) z ?_
    have := hgen (z ≫ jU) (z ≫ j₀) (by rw [Category.assoc, hjU, hz]) (by rw [Category.assoc, hj₀, hz])
    simpa only [Category.assoc] using this

  let G := (Over.pullback U.ι).obj H
  let G' := (Over.pullback c).obj A
  letI : (Over.pullback U.ι).Monoidal := (Over.instBraidedPullback (f := U.ι)).toMonoidal
  letI : GrpObj G := Functor.grpObjObj (F := Over.pullback U.ι) (G := H)
  letI : (Over.pullback c).Monoidal := (Over.instBraidedPullback (f := c)).toMonoidal
  letI : GrpObj G' := Functor.grpObjObj (F := Over.pullback c) (G := A)
  letI : (Over.pullback j₀).Monoidal := (Over.instBraidedPullback (f := j₀)).toMonoidal
  letI : GrpObj ((Over.pullback j₀).obj A₀) := Functor.grpObjObj (F := Over.pullback j₀) (G := A₀)
  have pH : IsGrpPullback ((Over.pullback j₀).obj A₀) H (jU ≫ U.ι) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₀).congr (hj₀.trans hjU.symm) rfl
  have pA : IsGrpPullback ((Over.pullback j₀).obj A₀) A (jU ≫ c) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₁).congr ha.symm rfl
  obtain ⟨φ, hφ⟩ := exists_isGrpPullback_cancel pH (isGrpPullback_pullback H U.ι)
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_cancel pA (isGrpPullback_pullback A c)

  haveI := isNoetherian_opens U
  haveI : IsDominant jU := ⟨jU.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG : IsSemiAbelian G := IsSemiAbelian.pullback U.ι H hH
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback c A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  obtain ⟨E, ⟨hE, -⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (isNormalScheme_opens hS U) hG' hG hψ hφ
  exact ⟨_, ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback H U.ι)).congr (Category.id_comp _) rfl⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EighthPowerUnits

section Rel

variable {S' S : Scheme.{0}} {j : S' ⟶ S} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem one_left_comp (hφ : IsGrpPullback G' G j φ) :
    (1 : G' ⟶ G').left ≫ φ = φ ≫ (1 : G ⟶ G).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  let z : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
    (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w]; rfl)
  have h := hφ.2 G' 1 1 z z rfl rfl
  rw [_root_.mul_one] at h
  have hz : z = 1 := mul_eq_left.1 (Over.OverMorphism.ext h)
  have h1 : φ₀ ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have h2 : z.left = (φ₀ ≫ (1 : G ⟶ G)).left := congrArg (fun w => w.left) (hz.trans h1.symm)
  rw [Over.comp_left] at h2
  exact h2

theorem mul_left_comp (hφ : IsGrpPullback G' G j φ) {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ * e₂).left ≫ φ = φ ≫ (F₁ * F₂).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  have h := hφ.2 G' e₁ e₂ (φ₀ ≫ F₁) (φ₀ ≫ F₂) h₁.symm h₂.symm
  rw [← MonObj.comp_mul] at h
  exact h.symm

theorem comp_left_comp {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ ≫ e₂).left ≫ φ = φ ≫ (F₁ ≫ F₂).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

end Rel

theorem exists_matrixUnits_extend : ∀ {S B : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U₀ : S.Opens) (hU : Dense (U₀ : Set S)) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (G' : Over U₀.toScheme) [GrpObj G'] (P : Over B) [GrpObj P] [IsCommMonObj P] (f : U₀.toScheme ⟶ B) (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G U₀.ι φ) (hψ : IsGrpPullback G' P f ψ) (E' : Fin 8 → Fin 8 → (P ⟶ P)) (hE' : ∀ a b, IsMonHom (E' a b)) (hrel : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1) (hsum : ∏ a, E' a a = 𝟙 P), ∃ E : Fin 8 → Fin 8 → (G ⟶ G), (∀ a b, IsMonHom (E a b)) ∧ (∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) ∧ ∏ a, E a a = 𝟙 G ∧ ∀ a b, ∃ e : G' ⟶ G', IsMonHom e ∧ e.left ≫ φ = φ ≫ (E a b).left ∧ e.left ≫ ψ = ψ ≫ (E' a b).left := by
  intro S B _ hS U₀ hU G _ _ hG G' _ P _ _ f φ ψ hφ hψ E' hE' hrel hsum
  have : IsDominant U₀.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS U₀.ι
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  let e : Fin 8 → Fin 8 → (G' ⟶ G') := fun a b =>
    Over.homMk (hψ.1.lift (ψ ≫ (E' a b).left) G'.hom (by rw [Category.assoc, Over.w, hψ.1.w]))
      (hψ.1.lift_snd _ _ _)
  have he : ∀ a b, (e a b).left ≫ ψ = ψ ≫ (E' a b).left := fun a b => hψ.1.lift_fst _ _ _
  have heM : ∀ a b, IsMonHom (e a b) := fun a b => by
    haveI := hE' a b
    exact ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback hψ hψ (E' a b) (e a b) (he a b)
  have uq : ∀ {x y : G' ⟶ G'} {F : P ⟶ P}, x.left ≫ ψ = ψ ≫ F.left → y.left ≫ ψ = ψ ≫ F.left → x = y :=
    fun hx hy => Over.OverMorphism.ext (hψ.1.hom_ext (hx.trans hy.symm) ((Over.w _).trans (Over.w _).symm))
  have uG : ∀ {F₁ F₂ : G ⟶ G}, φ ≫ F₁.left = φ ≫ F₂.left → F₁ = F₂ :=
    fun h => GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 h
  have ext : ∀ a b, ∃ F : G ⟶ G, IsMonHom F ∧ (e a b).left ≫ φ = φ ≫ F.left := fun a b => by
    haveI := heM a b
    exact (GlobalTheory.Published.SemiAbelianHomExtension.of_isGrpPullback GlobalTheory.semiAbelianHomExtension_holds hS hG hG hφ hφ
      (e a b)).exists
  choose E hE using ext
  refine ⟨E, fun a b => (hE a b).1, ?_, ?_, fun a b => ⟨e a b, heM a b, (hE a b).2, he a b⟩⟩
  · intro a b c d
    apply uG
    by_cases hbc : b = c
    · subst hbc
      rw [if_pos rfl]
      have h1 := comp_left_comp (he a b) (he b d)
      rw [hrel, if_pos rfl] at h1
      have h2 : e a b ≫ e b d = e a d := uq h1 (he a d)
      rw [← comp_left_comp (hE a b).2 (hE b d).2, h2, (hE a d).2]
    · rw [if_neg hbc]
      have h1 := comp_left_comp (he a b) (he c d)
      rw [hrel, if_neg hbc] at h1
      have h2 : e a b ≫ e c d = 1 := uq h1 (one_left_comp hψ)
      rw [← comp_left_comp (hE a b).2 (hE c d).2, h2, one_left_comp hφ]
  · have key : ∀ s : Finset (Fin 8), ∃ x : G' ⟶ G', x.left ≫ φ = φ ≫ (∏ a ∈ s, E a a).left ∧
        x.left ≫ ψ = ψ ≫ (∏ a ∈ s, E' a a).left := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · refine ⟨1, ?_, ?_⟩
        · rw [Finset.prod_empty]; exact one_left_comp hφ
        · rw [Finset.prod_empty]; exact one_left_comp hψ
      · intro a s ha ih
        obtain ⟨x, h1, h2⟩ := ih
        refine ⟨e a a * x, ?_, ?_⟩
        · rw [Finset.prod_insert ha]; exact mul_left_comp hφ (hE a a).2 h1
        · rw [Finset.prod_insert ha]; exact mul_left_comp hψ (he a a) h2
    obtain ⟨x, h1, h2⟩ := key Finset.univ
    rw [hsum] at h2
    have hx : x = 𝟙 G' := uq h2 (by simp)
    apply uG
    rw [← h1, hx]
    simp

end GlobalTheory.EighthPowerUnits
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isSemiAbelian_of_isGrpPullback_square : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S')
    [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → IsSemiAbelian G → IsSemiAbelian G' := by
  intro S S' f G _ G' _ F h hG
  have := hG.comm
  have : IsCommMonObj G' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigLBIso


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_rig_iso_of_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L₁ L₂ : RigLB G), LBIso L₁.L L₂.L → ∃ wL : LB.Iso L₁.L L₂.L, wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  rintro S G _ _ L₁ L₂ ⟨w, hw⟩
  let gv {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
    gm f y _ (w.s (j, k))

  have gm_isGen {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j j' : L.ι)
      (k k' : L'.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
      gv w f y j k = gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gv w f y j' k' := by
    have hV : f y ∈ (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L'.U k) (w.s (j, k)) =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L.U j') (L.g j j') *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
        res (inf_le_right : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j' ⊓ L'.U k') (w.s (j', k')) :=
      hw (j, k) (j', k')
    have key := congrArg (gm f y ((L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    rw [gm_res f y (U := L.U j ⊓ L'.U k) _ hV (w.s (j, k)),
      gm_res f y (U := L.U j' ⊓ L'.U k') _ hV (w.s (j', k'))] at key
    exact key

  let isoPullId {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) : LB.Iso L' (L.pull F) :=
    ⟨fun p => res (fun y hy => ⟨by have := mem_pull.1 hy.1; rw [hF] at this; exact this, hy.2⟩ :
      (LB.pull L F).U p.1 ⊓ L'.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L'.U p.2) (w.s (p.1 PUnit.unit, p.2))⟩

  have gw_isoPullId {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
      (j : L.ι) (k : L'.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L'.U k) :
      gw (isoPullId w hF) f y j k = gv w f y j k := by
    have hmem : f y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 (by rw [hF]; exact hj), hk⟩
    exact gm_res f y _ hmem (w.s (j, k))

  have isoPullId_pgen {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {F : X ⟶ X} (hF : F = 𝟙 X) :
      PGen (isoPullId w hF) := by
    intro Y f y j j' k k' hj hj' hk hk'
    subst hF
    rw [gw_isoPullId w rfl f y j k hj hk, gw_isoPullId w rfl f y j' k' hj' hk', Category.comp_id]
    exact gm_isGen hw f y j j' k k' hj hj' hk hk'

  have hw₀ : PGen (isoPullId w (F := 𝟙 G.left) rfl) := isoPullId_pgen hw rfl
  obtain ⟨c, hc⟩ := GlobalTheory.Unif.RigidifyIso.exists_ratio (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec G) (ε := fun _ => 1) hw₀ L₂.isLB L₁.isLB (𝟙 _)
    (fun _ => by rw [Category.comp_id, Category.id_comp]) L₁.rig L₁.rigGen L₂.rig L₂.rigGen
  let π : G.left ⟶ (𝟙_ (Over S)).left := G.hom
  have hs : eSec G ≫ π = 𝟙 _ := Over.w η[G]
  let wL : LB.Iso L₁.L L₂.L := ⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : L₂.L.ι) (k : L₁.L.ι), f y ∈ L₂.L.U j →
      f y ∈ L₁.L.U k → gv wL f y j k = gm (f ≫ π) y ⊤ c * gv w f y j k := by
    intro Y f y j k hj hk
    have hz : f y ∈ L₂.L.U j ⊓ L₁.L.U k := ⟨hj, hk⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res f y _ hz _).trans (gm_pull f π y ⊤ trivial c)) rfl)
  refine ⟨wL, ?_, ?_⟩
  · rintro p q
    apply unit_ext
    intro x hx
    have h1 : (𝟙 G.left) x ∈ L₂.L.U p.1 := hx.1.1
    have h2 : (𝟙 G.left) x ∈ L₁.L.U p.2 := hx.1.2
    have h3 : (𝟙 G.left) x ∈ L₂.L.U q.1 := hx.2.1
    have h4 : (𝟙 G.left) x ∈ L₁.L.U q.2 := hx.2.2
    have eL : gm (𝟙 G.left) x _ (res (inf_le_left : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s p)) =
        gv wL (𝟙 G.left) x p.1 p.2 := gm_res (𝟙 G.left) x _ hx _
    have eR : gm (𝟙 G.left) x _ ((L₂.L.div L₁.L).g p q *
        res (inf_le_right : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s q)) =
        gm (𝟙 G.left) x _ (L₂.L.g p.1 q.1) * (gm (𝟙 G.left) x _ (L₁.L.g p.2 q.2))⁻¹ * gv wL (𝟙 G.left) x q.1 q.2 :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L₁.L L₂.L (𝟙 G.left) x p q hx) (gm_res (𝟙 G.left) x _ hx _))
    rw [eL, eR, hv _ _ x _ _ h1 h2, hv _ _ x _ _ h3 h4, gm_isGen hw (𝟙 G.left) x p.1 q.1 p.2 q.2 h1 h3 h2 h4]
    exact mul_left_comm _ _ _
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hj : (eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk : (eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hj' : (𝟙 _ ≫ eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk' : (𝟙 _ ≫ eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hc' := hc _ (𝟙 _) x P Q (by simp only [Category.comp_id]; exact hx.1) hx.2
    have ep : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw (isoPullId w (F := 𝟙 G.left) rfl) (K := PUnit) (fun _ => eSec G) (fun _ => 1)
        (𝟙 _) x P Q = gv w (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) := by
      show ∏ k : PUnit, _ = _
      rw [Fintype.prod_unique, zpow_one]
      exact gw_isoPullId w rfl _ x _ _ hj' hk'
    rw [Category.comp_id, ep] at hc'
    have eL : gm (𝟙 _) x _ (res (inf_le_left : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _)
        (L₂.rig.s P)) = gm (𝟙 _) x _ (L₂.rig.s P) := gm_res (𝟙 _) x _ hx _
    have eR : gm (𝟙 _) x _ (@id (Γ((𝟙_ (Over S)).left, LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q)ˣ) ((LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) *
        res (inf_le_right : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _) (L₁.rig.s Q)) =
        gv wL (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) * gm (𝟙 _) x _ (L₁.rig.s Q) := by
      refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 _) x _ hx _))
      show gm (𝟙 _) x _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (wL.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res (𝟙 _) x _ hx _).trans (gm_pull (𝟙 _) (eSec G) x (L₂.L.U (P PUnit.unit) ⊓ L₁.L.U (Q PUnit.unit)) ⟨hj, hk⟩ _)
    refine eL.trans (hc'.trans (Eq.trans ?_ eR.symm))
    rw [hv _ _ x _ _ hj' hk', Category.assoc, hs, Category.comp_id]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.RigLBIso
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GrpPB

theorem isGrpPullback_comp {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {P : Over T} [GrpObj P] {f : S' ⟶ S} {t : T ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : P.left ⟶ G'.left}
    (h₁ : IsGrpPullback P G' t ψ) (h₂ : IsGrpPullback G' G f φ) :
    IsGrpPullback P G (t ≫ f) (ψ ≫ φ) := by
  refine ⟨h₁.1.paste_horiz h₂.1, fun T₀ x y x₀ y₀ hx hy => ?_⟩
  have wx : ∀ z : T₀ ⟶ P, (z.left ≫ ψ) ≫ G'.hom = (Over.mk (T₀.hom ≫ t)).hom := fun z => by
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w z]; rfl
  let x' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (x.left ≫ ψ) (wx x)
  let y' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (y.left ≫ ψ) (wx y)
  have e₁ : (x' * y').left = (x * y).left ≫ ψ := h₁.2 T₀ x y x' y' rfl rfl
  let e : Over.mk ((Over.mk (T₀.hom ≫ t)).hom ≫ f) ⟶ Over.mk (T₀.hom ≫ t ≫ f) :=
    Over.homMk (𝟙 _) (by simp)
  have e₂ : ((e ≫ x₀) * (e ≫ y₀)).left = (x' * y').left ≫ φ :=
    h₂.2 _ x' y' (e ≫ x₀) (e ≫ y₀) (by simp [e, x', hx]) (by simp [e, y', hy])
  rw [← MonObj.comp_mul, Over.comp_left] at e₂
  simp only [e, Over.homMk_left, Category.id_comp] at e₂
  rw [e₂, e₁, Category.assoc]

theorem baseChange_square {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (t : T ⟶ S') :
    IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧
      ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  have hc := isGrpPullback_comp (isGrpPullback_pullback G' t) h
  refine ⟨hc, ?_⟩
  set P := (Over.pullback t).obj G'
  have w : ∀ q : P ⊗ P ⟶ P, (q.left ≫ pullback.fst G'.hom t ≫ φ) ≫ G.hom = (Over.mk ((P ⊗ P).hom ≫ t ≫ f)).hom :=
    fun q => by
      rw [Category.assoc, Category.assoc, ← Category.assoc _ φ, hc.1.w, ← Category.assoc, Over.w q]; rfl
  let a : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (fst P P))
  let b : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (snd P P))
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]; rfl
  · rw [← Over.comp_left, lift_snd]; rfl

end GlobalTheory.GrpPB
end
