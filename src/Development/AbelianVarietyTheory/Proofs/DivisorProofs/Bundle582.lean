module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle530
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle531
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPullback_coprod_desc_of_pieces : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f : T ⟶ S) (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂), IsPullback v₁ f₁ f u₁ → IsPullback v₂ f₂ f u₂ → ∀ {X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂) (y : Y ⟶ T) (y₁ : Y₁ ⟶ T₁) (y₂ : Y₂ ⟶ T₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₁ ⟶ X₁) (i₂ : Y₂ ⟶ X₂), IsPullback j₁ y₁ y v₁ → IsPullback j₂ y₂ y v₂ → IsPullback i₁ y₁ x₁ f₁ → IsPullback i₂ y₂ x₂ f₂ → ∃ i : Y ⟶ X₁ ⨿ X₂, j₁ ≫ i = i₁ ≫ Limits.coprod.inl ∧ j₂ ≫ i = i₂ ≫ Limits.coprod.inr ∧ IsPullback i y (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) f := by
  intro S S₁ S₂ T T₁ T₂ u₁ u₂ hS v₁ v₂ hT f f₁ f₂ hf₁ hf₂ X₁ X₂ Y Y₁ Y₂ x₁ x₂ y y₁ y₂ j₁ j₂ i₁ i₂
    hj₁ hj₂ hi₁ hi₂
  obtain ⟨hS⟩ := hS
  obtain ⟨hT⟩ := hT
  obtain ⟨hY⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk j₁ j₂) y₁ y₂ y hj₁.w.symm hj₂.w.symm).mpr ⟨hj₁, hj₂⟩
  let x : X₁ ⨿ X₂ ⟶ S := Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)
  obtain ⟨hX₁, hX₂⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hS) (Limits.BinaryCofan.mk (Limits.coprod.inl : X₁ ⟶ X₁ ⨿ X₂)
    Limits.coprod.inr) x₁ x₂ x (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm).mp ⟨Limits.coprodIsCoprod X₁ X₂⟩
  obtain ⟨i, hi₁', hi₂'⟩ := Limits.BinaryCofan.IsColimit.desc' hY
    (i₁ ≫ Limits.coprod.inl) (i₂ ≫ Limits.coprod.inr)
  have e₁ : j₁ ≫ i = i₁ ≫ Limits.coprod.inl := hi₁'
  have e₂ : j₂ ≫ i = i₂ ≫ Limits.coprod.inr := hi₂'
  refine ⟨i, e₁, e₂, ?_⟩
  have H₁ : IsPullback (j₁ ≫ i) y₁ x (v₁ ≫ f) := by
    rw [e₁, hf₁.w]; exact hi₁.paste_horiz hX₁
  have H₂ : IsPullback (j₂ ≫ i) y₂ x (v₂ ≫ f) := by
    rw [e₂, hf₂.w]; exact hi₂.paste_horiz hX₂
  have w : i ≫ x = y ≫ f := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · change j₁ ≫ i ≫ x = j₁ ≫ y ≫ f
      rw [← Category.assoc j₁ i x, H₁.w, ← Category.assoc j₁ y f, hj₁.w, Category.assoc]
    · change j₂ ≫ i ≫ x = j₂ ≫ y ≫ f
      rw [← Category.assoc j₂ i x, H₂.w, ← Category.assoc j₂ y f, hj₂.w, Category.assoc]
  let c : Y ⟶ Limits.pullback x f := Limits.pullback.lift i y w
  have hcf : c ≫ Limits.pullback.fst x f = i := Limits.pullback.lift_fst _ _ _
  have hcs : c ≫ Limits.pullback.snd x f = y := Limits.pullback.lift_snd _ _ _
  have Q₁ : IsPullback (j₁ ≫ c) y₁ (Limits.pullback.snd x f) v₁ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₁)
      (by rw [Category.assoc, hcs]; exact hj₁.w)
      (IsPullback.of_hasPullback x f)
  have Q₂ : IsPullback (j₂ ≫ c) y₂ (Limits.pullback.snd x f) v₂ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₂)
      (by rw [Category.assoc, hcs]; exact hj₂.w)
      (IsPullback.of_hasPullback x f)
  obtain ⟨hP⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk (j₁ ≫ c) (j₂ ≫ c)) y₁ y₂ (Limits.pullback.snd x f)
    Q₁.w.symm Q₂.w.symm).mpr ⟨Q₁, Q₂⟩
  have hc : c = (hY.coconePointUniqueUpToIso hP).hom := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.left⟩).symm
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.right⟩).symm
  haveI : IsIso c := by rw [hc]; exact Iso.isIso_hom _
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) hcf hcs

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibreDense

theorem alg (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b : B)
    (h : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) : b = 0 := by
  by_contra hb
  let I : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hI : I ≠ ⊤ := by
    intro h1
    have : (1 : B) ∈ I := h1 ▸ Submodule.mem_top
    simp [I] at this
    exact hb this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  let u : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  obtain ⟨g, hg, hgQ⟩ := GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le A B b h u
  have h0 := GlobalTheory.T.nonZeroDivisor_localization_general_of_noetherian GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal A B b g u hg hgQ
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).1 h0
  exact s.2 (hle (by simpa [I] using hs))

theorem dense (X T : Scheme.{0}) (p : X ⟶ T) [Smooth p] (W : X.Opens)
    (hW : ∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) : IsSchemeTheoreticallyDominant W.ι := by
  refine GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective X T p W fun U V hU hV e b hb => ?_
  letI := (p.appLE V U e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(T, V) Γ(X, U) := HasRingHomProperty.appLE @Smooth p ‹_› ⟨V, hV⟩ ⟨U, hU⟩ e
  exact alg Γ(T, V) Γ(X, U) b (GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre X T p W U V hU hV e hW b hb)

theorem ext_of_dominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem main : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) [Smooth p] (q : Y ⟶ T) [IsSeparated q] (W : X.Opens),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ f g : X ⟶ Y, f ≫ q = g ≫ q → W.ι ≫ f = W.ι ≫ g → f = g := by
  intro X T Y p _ q _ W hW f g hfg hfgW
  haveI := dense X T p W hW
  exact ext_of_dominant q hfg W.ι hfgW

end GlobalTheory.FibreDense
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

theorem smooth_desc_of_isColimit : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  intro S S₁ S₂ X₁ X₂ u₁ u₂ ⟨hc⟩ x₁ x₂ h₁ h₂
  let e := Limits.IsColimit.coconePointUniqueUpToIso (Limits.coprodIsCoprod S₁ S₂) hc
  have e₁ : Limits.coprod.inl ≫ e.hom = u₁ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.left⟩
  have e₂ : Limits.coprod.inr ≫ e.hom = u₂ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.right⟩
  have i₁ : IsOpenImmersion (Limits.coprod.inl : S₁ ⟶ S₁ ⨿ S₂) := inferInstance
  have i₂ : IsOpenImmersion (Limits.coprod.inr : S₂ ⟶ S₁ ⨿ S₂) := inferInstance
  have : IsIso e.hom := Iso.isIso_hom e
  have ie : IsOpenImmersion e.hom := inferInstance
  have o₁ : IsOpenImmersion u₁ := e₁ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₁ ie)
  have o₂ : IsOpenImmersion u₂ := e₂ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₂ ie)
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (coprodOpenCover.{0, 0} X₁ X₂) ?_
  rintro (_ | _)
  · show Smooth (Limits.coprod.inl ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inl_desc]; infer_instance
  · show Smooth (Limits.coprod.inr ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inr_desc]; infer_instance

end GlobalTheory.ProdGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  first | exact @GlobalTheory.SmoothCrit.smooth_of_artinian_lift | exact GlobalTheory.SmoothCrit.smooth_of_artinian_lift | (intros; apply GlobalTheory.SmoothCrit.smooth_of_artinian_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by
  first | exact @GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson | exact GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson | (intros; apply GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

open Set Topology

namespace GlobalTheory.SpecGenClopen

theorem isClosed_of_stable (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Set X)
    (hs : StableUnderSpecialization T) (hg : StableUnderGeneralization T) : IsClosed T := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let T' : Set (U : Set X) := Subtype.val ⁻¹' T
  have key : ∀ Z : Set (U : Set X), IsIrreducible Z → (Z ∩ T').Nonempty → Z ⊆ T' := by
    rintro Z hZ ⟨t, htZ, htT⟩ z hz
    have hI : IsIrreducible (closure (Subtype.val '' Z : Set X)) :=
      (hZ.image _ continuous_subtype_val.continuousOn).closure
    obtain ⟨g₀, hg₀⟩ := QuasiSober.sober hI isClosed_closure
    have h1 : g₀ ⤳ (t : X) := hg₀.specializes (subset_closure ⟨t, htZ, rfl⟩)
    have h2 : g₀ ⤳ (z : X) := hg₀.specializes (subset_closure ⟨z, hz, rfl⟩)
    exact hs h2 (hg h1 htT)
  have hT' : T' = ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set X) | (Z ∩ T').Nonempty}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t,
      ⟨t, mem_irreducibleComponent, ht⟩⟩ mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨hZ, hZT⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact key Z hZ.1 hZT htZ
  have hc : IsClosed T' := by
    rw [hT']
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  refine ⟨Subtype.val '' T'ᶜ, ?_, U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hc.isOpen_compl, ⟨x, hxU⟩, hx, rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isClopen_of_specializes_iff : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Z : Set X),
    (∀ x y : X, x ⤳ y → (x ∈ Z ↔ y ∈ Z)) → IsClopen Z := by
  intro X _ Z h
  have hs : StableUnderSpecialization Z := fun x y hxy hx => (h x y hxy).1 hx
  have hg : StableUnderGeneralization Z := fun x y hxy hx => (h y x hxy).2 hx
  exact ⟨isClosed_of_stable X Z hs hg, isClosed_compl_iff.1 (isClosed_of_stable X Zᶜ
    (stableUnderSpecialization_compl_iff.2 hg) (stableUnderGeneralization_compl_iff.2 hs))⟩

end GlobalTheory.SpecGenClopen
end
end

section

open Complex Matrix

namespace GlobalTheory.ThetaDivisionPoints

theorem eq_zero_of_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {S : Set (Fin g → ℂ)}
    (hS : Submodule.span ℝ S = ⊤) {z : Fin g → ℂ}
    (hz : ∀ m ∈ S, (z ⬝ᵥ Hm.mulVec (star m)).im = 0) : z = 0 := by
  have h : ∀ m, (z ⬝ᵥ Hm.mulVec (star m)).im = 0 := by
    intro m
    have hm : m ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hz m hm
    | zero => simp
    | add a b _ _ ha hb => rw [star_add, mulVec_add, dotProduct_add, add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [star_smul, mulVec_smul, dotProduct_smul, smul_im, ha, smul_zero]
  by_contra hne
  have h1 := hpos z hne
  have h2 := h (I • z)
  rw [star_smul, mulVec_smul, dotProduct_smul] at h2
  simp at h2
  linarith

theorem exists_ne_zero_of_principal {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hχ : ∀ l, ‖χ l‖ = 1)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) (n : ℕ) (hn : 2 ≤ n) (f : (Fin g → ℂ) → ℂ)
    (hdf : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ (l : Λ) z, f (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f z) :
    ∃ l ∈ Λ, f ((n : ℂ)⁻¹ • l) ≠ 0 := by
  obtain ⟨φ, τ, Q, b, hτ, hτp, hΛ, hQ, -, hb, h1, h2⟩ :=
    GlobalTheory.SiegelNormalForm.exists_normal_form g Λ hd hs Hm χ Ef hH hpos hχ hE hbij
  have hφ : Differentiable ℂ (fun z => φ z) :=
    (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable
  have key := GlobalTheory.T.exists_theta_division_point_ne_zero g n τ (fun j => b j ^ n) (fun z => f (φ z) * cexp (-(n * Q z))) hτ hτp hn
    (fun j => pow_ne_zero _ (hb j)) ((hdf.comp hφ).mul ((hQ.const_mul (n : ℂ)).neg.cexp)) ?_ ?_ ?_
  · obtain ⟨m, k, h⟩ := key
    refine ⟨φ _, (hΛ _).2 ⟨m, k, rfl⟩, ?_⟩
    rw [← map_smul]
    exact left_ne_zero_of_mul h
  · intro h
    apply h0
    ext w
    have h := congrFun h (φ.symm w)
    simp only [Pi.zero_apply, LinearEquiv.apply_symm_apply] at h ⊢
    exact (mul_eq_zero.1 h).resolve_right (Complex.exp_ne_zero _)
  · intro i z
    have hm : φ (Pi.single i 1) ∈ Λ := by
      refine (hΛ _).2 ⟨Pi.single i 1, 0, ?_⟩
      ext a
      by_cases h : a = i
      · subst h; simp [Matrix.mulVec, dotProduct]
      · simp [h, Matrix.mulVec, dotProduct]
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h1 i ⟨_, hm⟩ z rfl] at e
    simp only [map_add (f := _)]
    rw [e, ← Complex.exp_nat_mul, mul_right_comm, ← Complex.exp_add, mul_comm]
    congr 2
    ring
  · intro j z
    have hm : φ (τ.mulVec (Pi.single j 1)) ∈ Λ := by
      refine (hΛ _).2 ⟨0, Pi.single j 1, ?_⟩
      have : (fun i => (((Pi.single j 1 : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
        ext a
        by_cases h : a = j
        · subst h; simp
        · simp [h]
      rw [this]
      ext a
      simp
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h2 j ⟨_, hm⟩ z rfl] at e
    simp only [map_add (f := _)]
    rw [e, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have : cexp (n * (Q (z + τ.mulVec (Pi.single j 1)) - Q z)) *
        cexp (-(n * Q (z + τ.mulVec (Pi.single j 1)))) = cexp (-(n * Q z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← this, show (n : ℂ) * (-(2 * Real.pi * I) * z j) = -(2 * Real.pi * I) * n * z j by ring]
    ring

theorem exists_ne_zero_of_selfDual : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (g : ℕ) (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)), Function.Injective p → ∀ L : Submodule ℤ V, L.FG → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) → Submodule.span ℝ (p '' (L : Set V)) = ⊤ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ N : ℕ, 2 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → f ≠ 0 → (∀ v ∈ L, ∀ z, f (z + p v) = c v * cexp (N * (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) + Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) → ∃ v ∈ L, f ((N : ℂ)⁻¹ • p v) ≠ 0 := by
  intro V _ _ _ g B p hp L hfg hL hsp Hm hH hpos hB c hc N hN f hdf h0 hf
  set Λ : Submodule ℤ (Fin g → ℂ) := L.map p with hΛ
  have hsp' : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := hsp
  choose q hq hpq using fun l : Λ => l.2
  have hint : ∀ l m : Λ, ∃ k : ℤ,
      (k : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := fun l m => by
    obtain ⟨k, hk⟩ := (hL _).1 (hq l) _ (hq m)
    exact ⟨k, by rw [← hpq l, ← hpq m, hB, hk, Rat.cast_intCast]⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ k
    (fun a b m => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, add_dotProduct, add_im]))
    (fun t a m => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, smul_dotProduct]; simp))
    (fun m a b => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, star_add, mulVec_add, dotProduct_add,
        add_im]))
    (fun t m a => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, star_smul, mulVec_smul,
        dotProduct_smul]; simp))
  have hE : ∀ l m : Λ, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := hk
  have hker : ∀ l : Λ, Ef l = 0 → l = 0 := fun l hl =>
    Subtype.ext (eq_zero_of_im_eq_zero hpos hsp' fun m hm => by
      rw [← hE l ⟨m, hm⟩, hl]; simp)
  have hdisc : DiscreteTopology Λ := by
    haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 (hfg.map p)
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := Λ)
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have e : ({0} : Set Λ) = ⋂ m ∈ s, {l : Λ |
        |((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im| < 1} := by
      ext l
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h m _ => by simp [h], fun h => hker l (LinearMap.ext_on hs fun m hm => ?_)⟩
      have h1 := h m hm
      rw [← hE, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h1
      exact Int.abs_lt_one_iff.1 h1
    rw [e]
    refine isOpen_biInter_finset fun m _ => isOpen_lt ?_ continuous_const
    refine (Complex.continuous_im.comp ?_).abs
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun u hu => hp ?_
    rw [map_zero]
    refine eq_zero_of_im_eq_zero hpos hsp ?_
    rintro _ ⟨v, -, rfl⟩
    rw [hB, hu]; simp
  have hBsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℚ) (V := V)).symm).1 hBinj
  have hbij : Function.Bijective Ef := by
    refine ⟨(injective_iff_map_eq_zero Ef).2 hker, fun φ => ?_⟩
    obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible ℚ).extension_property L.subtype
      L.subtype_injective ((Algebra.linearMap ℤ ℚ) ∘ₗ φ ∘ₗ p.submoduleMap L)
    obtain ⟨x, hx⟩ := hBsurj ψ.toAddMonoidHom.toRatLinearMap
    have h1 : ∀ (y) (hy : y ∈ L), B x y = (φ ⟨p y, Submodule.mem_map_of_mem hy⟩ : ℤ) :=
      fun y hy => by
        rw [hx]
        exact LinearMap.congr_fun hψ ⟨y, hy⟩
    refine ⟨⟨p x, Submodule.mem_map_of_mem ((hL x).2 fun y hy => ⟨_, h1 y hy⟩)⟩,
      LinearMap.ext ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    refine Int.cast_injective (α := ℝ) ?_
    rw [hE, hB, h1 y hy, Rat.cast_intCast]
  have hN0 : N ≠ 0 := by omega
  choose χ hχ using fun l : Λ => IsAlgClosed.exists_pow_nat_eq (c (q l)) (Nat.pos_of_ne_zero hN0)
  have hχ1 : ∀ l, ‖χ l‖ = 1 := fun l =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).1 (by rw [← norm_pow, hχ, hc])
  obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := exists_ne_zero_of_principal Λ hdisc hsp' Hm χ Ef hH hpos hχ1 hE
    hbij N hN f hdf h0 (fun l z => by
      rw [mul_pow, hχ, ← Complex.exp_nat_mul, ← hpq l]
      exact hf _ (hq l) z)
  exact ⟨v, hv, h⟩

end GlobalTheory.ThetaDivisionPoints
end

section


theorem _root_.GlobalTheory.T.local_max_principle_weighted_finiteType_int : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B], (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.local_max_principle_int | exact GlobalTheory.local_max_principle_int | (intros; apply GlobalTheory.local_max_principle_int <;> assumption)
end
