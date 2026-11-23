module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle923
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.FlagLocal

variable {X Y S : Scheme.{0}} {A A' A'' E E' : X.Modules}

theorem bijective_pullbackSections (a : Y ⟶ X) [IsOpenImmersion a] (E : X.Modules) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) :
    Function.Bijective (pullbackSections a E hW.le) := by
  subst hW
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction a) E
  have h1 : Function.Bijective (E.presheaf.map (homOfLE (a.image_preimage_le V)).op) :=
    QCoh.res_bijective_of_eq E _ (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_eq_right.2 hV)
  have h2 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback a).hom.app E).app (a ⁻¹ᵁ V))
  convert h2.comp h1 using 1
  funext s
  exact (resM_self _ _).trans congr(($e).app V s).symm

theorem mem_range_of_pullback (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) (t : Γ(E, V))
    (h : ∃ m, ((Scheme.Modules.pullback a).map v).app W m = pullbackSections a E hW.le t) :
    ∃ m, v.app V m = t := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m, rfl⟩ := (bijective_pullbackSections a A hV hW).2 m
  rw [pullback_map_app_pullbackSections] at hm
  exact ⟨m, (bijective_pullbackSections a E hV hW).1 hm⟩

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

variable {G : ∀ i, (T i).Modules} (v : ∀ i, G i ⟶ (Scheme.Modules.pullback (a i)).obj E)


end Cover

end GlobalTheory.FlagLocal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.finrank_hom_harrisTaylorOrder_morita : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k], (∀ n : ℕ, n.Coprime p → (n : k) ≠ 0) → ∀ (χ : 𝓞 D.F →+* k) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (σX : D.O →+* Module.End k X) (σY : D.O →+* Module.End k Y), (∀ c, σX (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → (∀ c, σY (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → D.m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO σX σY) = Module.finrank k X * Module.finrank k Y := by
  first | (exact @GlobalTheory.HTRho.finrank_homO_morita) | (exact GlobalTheory.HTRho.finrank_homO_morita) | (intros; apply GlobalTheory.HTRho.finrank_homO_morita <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem mvRefine (L1 : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0) (L2 : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a) : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  intro q A A' _ _ _ f hA' n i x hx1 hx2
  obtain ⟨δ, hδex, hδref⟩ := L1 q A A' f hA' n i
  obtain ⟨w, rfl⟩ := (hδex x).1 (by simp [hx1, hx2])
  refine ⟨w, ?_⟩
  intro g hfg A₂ C _ _ _ _ _ _ hA₂ hg hC a ha hcomp
  obtain ⟨b, hb⟩ := L2 q A C f g hfg hC n i a ha
  have hf2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hg2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ g)) := hg.map _
  let φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (algebraMap A A' f)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A' A₂))
      (by simpa [← IsScalarTower.algebraMap_apply] using hf2)
  let ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (f * g)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A A₂))
      (by simpa using hf2.mul hg2)
  have hfg' : IsUnit (algebraMap A (Localization.Away (f * g)) f) :=
    isUnit_of_mul_isUnit_left (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * g)) (f * g))
  let ρ : Localization.Away f →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift f (g := algebraMap A (Localization.Away (f * g))) hfg'
  have hφ : φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) := IsLocalization.Away.lift_comp _ _
  have hψ : ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) := IsLocalization.Away.lift_comp _ _
  have hρ : ρ.comp (algebraMap A _) = algebraMap A _ := IsLocalization.Away.lift_comp _ _
  have hψρ : ψ.comp ρ = Localization.awayMap (algebraMap A A₂) f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, hρ, hψ]
    exact (IsLocalization.map_comp _).symm
  refine hδref A₂ hA₂ φ hφ w b ?_
  rw [hcomp φ ψ hφ hψ, ← hb ρ hρ, ← pull_comp, ← spMap_comp_ring, hψρ]

theorem mvRefine_main : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := mvRefine GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd GlobalTheory.T.mayerVietoris_extend_class_coprime_etaleExcision

end GlobalTheory.EtC
end

section

namespace GlobalTheory.EtC

theorem kummer_divisor_step : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro q k B _ _ _ _ _ _ hq f hf A₂ _ _ hA c
  obtain ⟨b₁, m, e, he, hc⟩ := GlobalTheory.T.exists_unit_form_localization_etale_nbhd B A₂ f hA c
  by_cases hb : b₁ = 0
  · refine ⟨1, isCoprime_one_right, 1, ?_, ⟨B, inferInstance, inferInstance, isExcisionNbhd_self B 1, 1, by simp⟩⟩
    have hL := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA e 1 (by simpa using he)
    refine ⟨Localization.Away e, inferInstance, inferInstance, inferInstance, inferInstance, hL, by simp, 1, ?_⟩
    intro φ ψ hφ hψ
    subst hb
    have hc' := congrArg φ hc
    simp only [map_zero, map_mul, map_pow] at hc'
    have hx : IsUnit (φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) e) *
        φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f)) ^ m) := by
      have h1 : ∀ y : A₂, φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) y) =
          algebraMap (Localization.Away e) _ (algebraMap A₂ (Localization.Away e) y) := fun y => by
        rw [← RingHom.comp_apply, hφ]; rfl
      rw [h1, h1]
      refine IsUnit.mul ((IsLocalization.Away.algebraMap_isUnit e).map _) (IsUnit.pow _ ?_)
      rw [← IsScalarTower.algebraMap_apply]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (Localization.Away e) f)) (algebraMap B (Localization.Away e) f)
    have hu := (c.isUnit.map φ).mul hx
    rw [← hc'] at hu
    haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
    exact Subsingleton.elim _ _
  · obtain ⟨g, hg0, hfg, u, n, d, t, n', d', hn, hd, hn', hd', h1, h2⟩ := GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition k B q hq f hf b₁ hb m
    exact ⟨g, hfg, u, GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus k B q hq f hf A₂ hA c b₁ m e he hc g hfg u n d hn hd h1,
      GlobalTheory.T.coprime_unit_etale_extension k B q hq f g hg0 u t n' d' hn' hd' h2⟩

end GlobalTheory.EtC
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstOrigin : GlobalTheory.VertUnits.DivConstOrigin := by
  have h₁ := GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin
  have h₂ := GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants
  have h₃ := GlobalTheory.T.divConst_origin_noeth_alt
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith GlobalTheory.VertUnits.DivConst
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh _ hPo b c s hs hbc
  have hPo' : P = GlobalTheory.KeyOriginCut.originIdeal T := hPo
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, b₁, c₁, hbc₁, hjb, hjc⟩ :=
    h₁ T O hT P φ hφ hsh hPo' b c s hs hbc
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, bA, cA, sA, hsA, hisA,
    hbcA, hjbA⟩ := h₂ T O hT E Q hQ j hj b₁ c₁ s hs hbc₁
  obtain ⟨a, w, haw⟩ := h₃ T O hT P φ hφ hsh hPo' A i hi hil EA QA hQA jA hjA bA cA sA hsA hbcA
  exact ⟨a, w, by rw [← hjb, ← hjbA, haw]⟩

end GlobalTheory.VertUnits
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (Q : ℕ) (h : IsUnit (Q : Γ(U, ⊤))) :
    IsUnit (Q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_defectSec : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) →
    ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
      Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  intro Q q _ hqQ U u hQ

  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ Q = Units.map g.appTop.hom.toMonoidHom u
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => defect Q q V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hQV : IsUnit (Q : Γ(V, ⊤)) := isUnit_natCast_appTop g Q hQ
    have hQW : IsUnit (Q : Γ(W, ⊤)) := isUnit_natCast_appTop k Q hQV
    change Sec.res k (defect Q q V hg.choose) = defect Q q W (S.downward_closed hg k).choose
    rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W V k hg.choose hQV]
    refine GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ W _ _ hQW ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).2 S hS s hcompat
  have hex : ∃ a : Sec ((res _ (tw q 1)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ),
      v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = defect Q q V v := by
    refine ⟨a, fun V g v hv => ?_⟩
    have hg : S.arrows g := ⟨v, hv⟩
    rw [ha V g hg]
    exact GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ V _ _ (isUnit_natCast_appTop g Q hQ) (hg.choose_spec.trans hv.symm)
  intro V g v hv
  exact pick_spec hex V g v hv

end GlobalTheory.EtC.RedChern
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

noncomputable section

namespace GlobalTheory.EtC.KumPic

section
variable (q : ℕ) [NeZero q]

theorem prim_pow_eq_one {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hr
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

def primUnit {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q (prim_pow_eq_one q ζ) (NeZero.ne q)

theorem primUnit_val {A : Type} [CommRing A] (ζ : Prim q A) : ((primUnit q ζ : Aˣ) : A) = ζ.1 :=
  Units.val_ofPowEqOne _ _ _ _

theorem dv_res (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤)))
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dv q φ U v) = dv q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold dv
  rw [show ∀ a b : Sec ((res ℤ (twZ q)).X 0) U, Sec.res g (a - b) = Sec.res g a - Sec.res g b from
    fun a b => LinearMap.map_sub _ a b, PicSpec.sec_map_res, PicSpec.unitSec_res, (restrMap _ _).nat, (kumT_spec q).1 V U g v hq]

variable (κ : twZ q ⟶ Gm)
  (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
    Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u)
  (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (hφ : κ ≫ φ = resι ℤ (twZ q))
include hκ hφ

theorem dv_mul_prim {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) :
    dv q φ U w = dv q φ U v := by
  have hu := primUnit_val q ζ
  have hw : w = primUnit q ζ * v := Units.ext (by rw [Units.val_mul, hu, h])
  have hk := (kumT_spec q).2 U ζ v w h
  have h1 : Sec.map φ (unitSec (primUnit q ζ)) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) := by
    rw [← hκ U ζ _ hu, PicSpec.sec_map_comp, hφ]
  have h2 : (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (resGen 1 ζ) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) :=
    restrMap_spec _ _ U _
  unfold dv
  rw [hk, map_add (f := _), h2, hw, PicSpec.unitSec_mul, PicSpec.sec_map_add, h1]
  abel

theorem dv_mul_prim_pow {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v → dv q φ U w = dv q φ U v := by
  induction a with
  | zero =>
    intro v w h
    rw [pow_zero, one_mul] at h
    rw [Units.ext h]
  | succ a ih =>
    intro v w h
    have h1 : ((primUnit q ζ ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, primUnit_val]
    rw [dv_mul_prim q κ hκ φ hφ ζ (primUnit q ζ ^ a * v) w (by rw [h, h1, pow_succ', mul_assoc]), ih v (primUnit q ζ ^ a * v) h1]

end

theorem dv_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  intro q _ κ hκ φ hφ U hq v v' hvv
  have sep := fun W : Scheme.{0} => (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ ((res ℤ (twZ q)).X 0) W).1
  apply sep U
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  rw [dv_res q φ g hq, dv_res q φ g hq]
  set x := Units.map g.appTop.hom.toMonoidHom v
  set x' := Units.map g.appTop.hom.toMonoidHom v'
  have hx : x ^ q = x' ^ q := by simp only [x, x', ← map_pow, hvv]
  apply sep V
  have hω : ((x' * x⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hx, inv_pow, mul_inv_cancel, Units.val_one]
  obtain ⟨S₂, hS₂, hP₂⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ _ hω
  refine ⟨S₂, hS₂, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP₂ W h hh
  rw [dv_res q φ h hqV, dv_res q φ h hqV]
  symm
  apply dv_mul_prim_pow q κ hκ φ hφ (ζ.map h.appTop.hom) a
  change h.appTop.hom (x' : Γ(V, ⊤)) = (h.appTop.hom ζ.1) ^ a * h.appTop.hom (x : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.EtC.KumPic

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

noncomputable section
namespace GlobalTheory.EtC.KumPic.DvGlue

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (h : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem dv_res (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ)
    (hq : IsUnit (q : Γ(U, ⊤))) :
    Sec.res g (dv q φ U v) = dv q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold dv
  rw [show ∀ a b : Sec ((res ℤ (twZ q)).X 0) U, Sec.res g (a - b) = Sec.res g a - Sec.res g b from
    fun a b => map_sub _ a b]
  rw [PicSpec.sec_map_res, PicSpec.unitSec_res, SemiMap.nat, (kumT_spec q).1 V U g v hq]

theorem glue : ∀ (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v') → ∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v := by
  intro q _ φ hdv U b hq
  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom b
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq b
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res ℤ (twZ q)).X 0) V :=
    fun V g hg => dv q φ V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hqV : IsUnit (q : Γ(V, ⊤)) := isUnit_natCast_appTop g q hq
    have hqW : IsUnit (q : Γ(W, ⊤)) := isUnit_natCast_appTop k q hqV
    change Sec.res k (dv q φ V hg.choose) = dv q φ W (S.downward_closed hg k).choose
    rw [dv_res q φ k hg.choose hqV]
    refine hdv W hqW _ _ ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).2 S hS s hcompat
  refine ⟨a, fun V g v hv => ?_⟩
  have hg : S.arrows g := ⟨v, hv⟩
  rw [ha V g hg]
  exact hdv V (isUnit_natCast_appTop g q hq) _ _ (hg.choose_spec.trans hv.symm)

end GlobalTheory.EtC.KumPic.DvGlue
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.integralClosureEtaleAt_of_height_le_one_purity : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime], P.height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one) | (exact GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one) | (intros; apply GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.testHom_matrix_generates_normalised : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c ∧ GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c ∧ GlobalTheory.HomFixUniv.Normal t c αA βB := by
  first | (exact @GlobalTheory.HomFixMatCond.mat_cond) | (exact GlobalTheory.HomFixMatCond.mat_cond) | (intros; apply GlobalTheory.HomFixMatCond.mat_cond <;> assumption)
end
