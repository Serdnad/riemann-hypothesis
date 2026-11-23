module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle050
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle008
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.VertFib

abbrev epsPt : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

abbrev epsStr : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ))

def ringVal {A : Type} [CommRing A] {X : Scheme.{0}} (v : Sp A ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((v.appLE W ⊤ h).hom f)

theorem epsPt_epsStr : epsPt ≫ epsStr = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem top_le_of_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W) : ⊤ ≤ v ⁻¹ᵁ W := by
  intro q _
  have hq : (q : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
    intro x hx
    have hx0 : TrivSqZeroExt.fst x = 0 := hx
    apply q.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two]; ext <;> simp [hx0]
    rw [this]; exact q.asIdeal.zero_mem
  obtain ⟨s, rfl⟩ := hq
  exact h (Set.mem_univ s)

theorem top_le_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W := fun _ _ => h (Set.mem_univ _)

theorem ringVal_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (O : Y.Opens)
    (e : O ≤ m ⁻¹ᵁ W) (h : ⊤ ≤ v ⁻¹ᵁ O) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v O h ((m.appLE W O e).hom f) = ringVal (v ≫ m) W h' f := by
  rw [ringVal, ringVal, ← CommRingCat.comp_apply (m.appLE W O e), Scheme.Hom.appLE_comp_appLE]

theorem ringVal_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ (m ⁻¹ᵁ W)) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v (m ⁻¹ᵁ W) h ((m.app W).hom f) = ringVal (v ≫ m) W h' f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ringVal_appLE v m W _ _ h h' f

theorem ringVal_spMap {A R : Type} [CommRing A] [CommRing R] (φ : R →+* A) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (s : Γ(Sp R, ⊤)) :
    ringVal (spMap φ) ⊤ h s = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom s) h1
  have h3 : (spMap φ).appLE ⊤ ⊤ h = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
  rw [ringVal, h3]
  exact h2

theorem ringVal_congr {A : Type} [CommRing A] {X : Scheme.{0}} {v v' : Sp A ⟶ X} (e : v = v') (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v' ⁻¹ᵁ W) (f : Γ(X, W)) : ringVal v W h f = ringVal v' W h' f := by
  subst e; rfl

theorem ringVal_constFn {A R : Type} [CommRing A] [CommRing R] {X : Scheme.{0}} (v : Sp A ⟶ X) (p : X ⟶ Sp R)
    (φ : R →+* A) (hv : v ≫ p = spMap φ) (h : ⊤ ≤ v ⁻¹ᵁ ⊤) (r : R) :
    ringVal v ⊤ h (constFn p ⊤ r) = φ r := by
  refine (ringVal_appLE v p ⊤ ⊤ le_top h le_top _).trans ?_
  refine (ringVal_congr hv ⊤ _ le_top _).trans ((ringVal_spMap φ _ _).trans ?_)
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r

theorem snd_ringVal_const {X : Scheme.{0}} (z : Sp ℂ ⟶ X) (W : X.Opens) (h : ⊤ ≤ (epsStr ≫ z) ⁻¹ᵁ W) (f : Γ(X, W)) :
    TrivSqZeroExt.snd (ringVal (epsStr ≫ z) W h f) = 0 := by
  have hz : ⊤ ≤ z ⁻¹ᵁ W := by
    have := top_le_epsPt _ W h
    rwa [← Category.assoc, epsPt_epsStr, Category.id_comp] at this
  exact congrArg TrivSqZeroExt.snd
    ((ringVal_appLE epsStr z W ⊤ hz le_top h f).symm.trans (ringVal_spMap _ _ _))

theorem comp_eq_const {R : Type} [CommRing R] (x₀ : R →+* ℂ) {X : Scheme.{0}} (p : X ⟶ Sp R)
    (v : Sp (DualNumber ℂ) ⟶ X) (h₁ : epsPt ≫ v ≫ p = spMap x₀)
    (h₂ : ∀ r, TrivSqZeroExt.snd (ringVal v ⊤ le_top (constFn p ⊤ r)) = 0) :
    v ≫ p = epsStr ≫ spMap x₀ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (v ≫ p)
  have hφ : v ≫ p = spMap ψ.hom := hψ.symm
  rw [hφ, ← Spec.map_comp] at h₁
  have h₃ := Spec.map_injective h₁
  rw [hφ, ← Spec.map_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  have h₄ : TrivSqZeroExt.snd (ψ.hom r : DualNumber ℂ) = 0 :=
    (congrArg TrivSqZeroExt.snd (ringVal_constFn v p ψ.hom hφ le_top r)).symm.trans (h₂ r)
  have h₅ : TrivSqZeroExt.fst (ψ.hom r : DualNumber ℂ) = x₀ r := congrArg (fun g => g.hom r) h₃
  exact TrivSqZeroExt.ext h₅ h₄

end GlobalTheory.KS.VertFib


open GlobalTheory.KS.VertFib in
theorem GlobalTheory.KS.ptDer_of_fibre : ∀ (Y : Over (Sp ℂ)) (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y.left ⟶ X), IsPullback m Y.hom p (spMap x₀) → ∀ y : Sp ℂ ⟶ Y.left, y ≫ Y.hom = 𝟙 _ → (∀ δ, PtDer (y ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃ δ₀, PtDer y δ₀ ∧ (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) ∧ ∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ W f = δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f)) ∧ ∀ δ₀, PtDer y δ₀ → (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) → (∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f) = 0) → ∀ O f, ⊤ ≤ y ⁻¹ᵁ O → δ₀ O f = 0 := by
  intro Y R _ x₀ X p m hP y hy
  constructor
  · intro δ hδ h0
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 δ hδ
    have hvp : v ≫ p = epsStr ≫ spMap x₀ := by
      refine comp_eq_const x₀ p v ?_ fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rw [← Category.assoc, hv, Category.assoc, hP.w, ← Category.assoc, hy, Category.id_comp]
    have hw₁ := hP.lift_fst v epsStr hvp
    have hw₂ := hP.lift_snd v epsStr hvp
    generalize hP.lift v epsStr hvp = w at hw₁ hw₂
    have hwy : epsPt ≫ w = y := by
      apply hP.hom_ext
      · rw [Category.assoc, hw₁, hv]
      · rw [Category.assoc, hw₂, epsPt_epsStr, hy]
    obtain ⟨δ₀, hδ₀, hw⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).2 w hwy
    refine ⟨δ₀, hδ₀, fun a => ?_, fun W f hW => ?_⟩
    · refine (hw ⊤ le_top _).symm.trans ?_
      exact congrArg TrivSqZeroExt.snd (ringVal_constFn w Y.hom _ hw₂ le_top a)
    · have h1 : ⊤ ≤ v ⁻¹ᵁ W := top_le_of_epsPt v W (by rw [hv]; exact hW)
      have h2 : ⊤ ≤ (w ≫ m) ⁻¹ᵁ W := by rw [hw₁]; exact h1
      refine (hvδ W h1 f).symm.trans (Eq.trans ?_ (hw (m ⁻¹ᵁ W) h2 _))
      exact congrArg TrivSqZeroExt.snd
        ((ringVal_congr hw₁.symm W h1 h2 f).trans (ringVal_app w m W h2 h2 f).symm)
  · intro δ₀ hδ₀ h0 hm O f hO
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).1 δ₀ hδ₀
    have hvp : v ≫ Y.hom = epsStr := by
      have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
      have := comp_eq_const (RingHom.id ℂ) Y.hom v (by rw [← Category.assoc, hv, hy, hid])
        fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rwa [hid, Category.comp_id] at this
    have hz : PtDer (y ≫ m) (fun _ _ => 0) := ⟨by simp, by simp, by simp⟩
    have hvm : v ≫ m = epsStr ≫ y ≫ m := by
      refine ((GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 _ hz).unique ⟨?_, fun W h g => ?_⟩ ⟨?_, fun W h g => ?_⟩
      · rw [← Category.assoc, hv]
      · have hW : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W := by
          have := top_le_epsPt _ W h
          rwa [← Category.assoc, hv] at this
        refine Eq.trans ?_ ((hvδ (m ⁻¹ᵁ W) h _).trans (hm W g hW))
        exact congrArg TrivSqZeroExt.snd (ringVal_app v m W h h g).symm
      · rw [← Category.assoc, epsPt_epsStr, Category.id_comp]
      · exact snd_ringVal_const (y ≫ m) W h g
    have hvc : v = epsStr ≫ y := by
      apply hP.hom_ext
      · rw [hvm, Category.assoc]
      · rw [hvp, Category.assoc, hy, Category.comp_id]
    have h1 : ⊤ ≤ v ⁻¹ᵁ O := top_le_of_epsPt v O (by rw [hv]; exact hO)
    refine (hvδ O h1 f).symm.trans ?_
    have h2 : ⊤ ≤ (epsStr ≫ y) ⁻¹ᵁ O := by rw [← hvc]; exact h1
    exact (congrArg TrivSqZeroExt.snd (ringVal_congr hvc O h1 h2 f)).trans (snd_ringVal_const y O h2 f)

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LinDescent

private lemma isOpenImmersion_of_section_of_etale' {X Y : Scheme.{0}} (s : Y ⟶ X) (g : X ⟶ Y)
    [Etale g] (h : s ≫ g = 𝟙 Y) : IsOpenImmersion s := by
  have hP : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr fun _ _ f hf => by
      have : Etale f := hf
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  refine MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) s g inferInstance ?_
  rw [h]
  infer_instance

private lemma exists_mem_range_lift_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) (p : ↥(pullback π π)) :
    ∃ a, p ∈ Set.range ⇑(pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) :
      X ⟶ pullback π π) := by
  let K := AlgebraicClosure ((pullback π π).residueField p)
  let q : Spec (CommRingCat.of K) ⟶ pullback π π :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑((pullback π π).residueField p) K)) ≫ (pullback π π).fromSpecResidueField p
  obtain ⟨a, ha, -⟩ := h.fibre K (q ≫ pullback.snd π π) (q ≫ pullback.fst π π)
    (by simp only [Category.assoc, pullback.condition])
  let x : ↥(Spec (CommRingCat.of K)) := show PrimeSpectrum K from IsLocalRing.closedPoint K
  refine ⟨a, (q ≫ pullback.snd π π) x, ?_⟩
  have e : (q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) = q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  have hq : q x = p := by
    have hx : q x ∈ Set.range ((pullback π π).fromSpecResidueField p) :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [Scheme.range_fromSpecResidueField] at hx
    exact Set.mem_singleton_iff.mp hx
  calc _ = ((q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X)
        (by rw [h.inv a, Category.id_comp])) x := (Scheme.Hom.comp_apply _ _ _).symm
    _ = q x := by rw [e]
    _ = p := hq

theorem locTransitive_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) : LocTransitive ρ π := by
  intro Z g₁ g₂ hg z
  let φ : Z ⟶ pullback π π := pullback.lift g₁ g₂ hg
  obtain ⟨c, hc⟩ := exists_mem_range_lift_of_isGaloisCover h (φ z)
  let gr : X ⟶ pullback π π := pullback.lift (ρ c) (𝟙 X) (by rw [h.inv c, Category.id_comp])
  have : Etale π := h.etale
  have : IsOpenImmersion gr :=
    isOpenImmersion_of_section_of_etale' gr (pullback.snd π π) (pullback.lift_snd _ _ _)
  let U : Z.Opens := φ ⁻¹ᵁ gr.opensRange
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range gr := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact v.2
  let lw := IsOpenImmersion.lift gr (U.ι ≫ φ) hr
  have hw : lw ≫ gr = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨c, U.toScheme, U.ι, inferInstance, ⟨z, hc⟩, rfl, ?_⟩
  have h1 : U.ι ≫ g₁ = lw ≫ ρ c := by
    have e := congrArg (· ≫ pullback.fst π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_fst] at e
    exact e.symm
  have h2 : U.ι ≫ g₂ = lw := by
    have e := congrArg (· ≫ pullback.snd π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_snd, Category.comp_id] at e
    exact e.symm
  rw [h1, h2]

theorem exists_descent_of_isGaloisCover :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  intro X Y π Ga _ ρ L hG hL u hu hc
  have : Finite Ga := hG.finite
  have : IsFinite π := hG.fin
  have : Etale π := hG.etale
  have : Surjective π := hG.onto
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ ρ c := by
    intro k _ _ r a b hab
    obtain ⟨d, -, hd⟩ := hG.fibre k r (r ≫ ρ a) (by rw [Category.assoc, hG.inv])
    exact (hd a rfl).trans (hd b hab.symm).symm
  exact exists_descent_of_galois hL hG.one (fun a c => (hG.mul a c).symm) hG.inv
    (locTransitive_of_isGaloisCover hG) hfree hu hc

end GlobalTheory.LinDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace

theorem baseChange_appLE_chartAlgEquiv {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (i : Fin (N + 1)) (q : MvPolynomial {j // j ≠ i} R) :
    ((baseChange N φ).appLE (chart R N i) (chart R' N i) (baseChange_preimage_chart N φ i).ge).hom
      (chartAlgEquiv R N i q) = chartAlgEquiv R' N i (MvPolynomial.map φ q) := by
  have h : ((baseChange N φ).appLE (chart R N i) (chart R' N i)
      (baseChange_preimage_chart N φ i).ge).hom.comp (RingHomClass.toRingHom (chartAlgEquiv R N i)) =
      (RingHomClass.toRingHom (chartAlgEquiv R' N i)).comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_C]
      have h1 : chartAlgEquiv R N i (MvPolynomial.C r) = _ := (chartAlgEquiv R N i).commutes r
      have h2 : chartAlgEquiv R' N i (MvPolynomial.C (φ r)) = _ := (chartAlgEquiv R' N i).commutes (φ r)
      rw [h1, h2, ← formOn_C (i := i) (hi := le_rfl), ← formOn_C (i := i) (hi := le_rfl)]
      have h3 := baseChange_app_formOn φ (le_refl (chart R N i)) (MvPolynomial.isHomogeneous_C _ r)
      refine (congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3).trans ?_
      rw [resG_formOn]
      congr 1
      exact MvPolynomial.map_C _ _
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_X, chartAlgEquiv_X]
      have h3 := baseChange_app_ratioOn φ (le_refl (chart R N i)) j.1
      exact congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3
  exact congrArg (fun ψ => ψ q) h


set_option backward.isDefEq.respectTransparency false in
theorem comap_map_baseChange {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (I : (PSpace R' N).IdealSheafData) (T : ∀ i : Fin (N + 1), Set (MvPolynomial {j // j ≠ i} R'))
    (hT : ∀ i, Ideal.span (chartAlgEquiv R' N i '' T i) = I.ideal ⟨_, isAffineOpen_chart R' N i⟩)
    (hφ : ∀ i, T i ⊆ Set.range (MvPolynomial.map φ)) :
    (I.map (baseChange N φ)).comap (baseChange N φ) = I := by
  have : IsAffineHom (baseChange N φ) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChange N φ).flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun i => ⟨_, isAffineOpen_chart R' N i⟩) (iSup_chart R' N) fun i => ?_
  rw [← hT, Ideal.span_le]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨q, rfl⟩ := hφ i ht
  have h0 : chartAlgEquiv R' N i (MvPolynomial.map φ q) ∈ I.ideal ⟨_, isAffineOpen_chart R' N i⟩ := by
    rw [← hT]
    exact Ideal.subset_span ⟨_, ht, rfl⟩
  rw [← baseChange_appLE_chartAlgEquiv] at h0 ⊢
  refine GlobalTheory.GaloisDescent.ideal_le_comap_appLE (baseChange N φ) le_rfl ⟨_, isAffineOpen_chart R N i⟩
    ⟨_, isAffineOpen_chart R' N i⟩ (baseChange_preimage_chart N φ i).ge ?_
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, Ideal.mem_comap]
  have h1 := I.ideal_le_comap_ideal
    (U := ⟨_, (isAffineOpen_chart R N i).preimage (baseChange N φ)⟩)
    (V := ⟨_, isAffineOpen_chart R' N i⟩) (baseChange_preimage_chart N φ i).le h0
  rw [Ideal.mem_comap, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h1
  rw [Scheme.Hom.app_eq_appLE]
  exact h1

end GlobalTheory.ProjSpace

namespace GlobalTheory


open ProjSpace in
theorem exists_finset_isProjOver_descends : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  classical
  rintro K _ K₀ X p ⟨N, e, he, rfl⟩
  have hT : ∀ i : Fin (N + 1), ∃ T : Finset (MvPolynomial {j // j ≠ i} K),
      Ideal.span (chartAlgEquiv K N i '' T) = e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩ := fun i => by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian
      ((e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩).comap (chartAlgEquiv K N i)))
    refine ⟨T, ?_⟩
    have := congrArg (Ideal.map (chartAlgEquiv K N i)) hT
    rw [Ideal.map_comap_of_surjective _ (chartAlgEquiv K N i).surjective] at this
    rw [← this]
    exact (Ideal.map_span _ _).symm
  choose T hT using hT
  refine ⟨Finset.univ.biUnion fun i => (T i).biUnion MvPolynomial.coeffs, fun K₁ _ hs => ?_⟩
  have key := comap_map_baseChange N K₁.subtype e.ker (fun i => T i) hT fun i t ht => by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.2
    intro c hc
    refine ⟨⟨c, hs ?_⟩, rfl⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, t, ht, hc⟩
  rw [Scheme.IdealSheafData.map_ker] at key
  refine ⟨(e ≫ baseChange N K₁.subtype).image, (e ≫ baseChange N K₁.subtype).imageι ≫ PSpace.str K₁ N,
    (e ≫ baseChange N K₁.subtype).toImage, ⟨N, _, inferInstance, rfl⟩, ?_⟩
  have h := isPullback_of_isClosedImmersion e (e ≫ baseChange N K₁.subtype).imageι
    (e ≫ baseChange N K₁.subtype).toImage (baseChange N K₁.subtype) (by simp)
    (by rw [← key]; congr 1; exact Scheme.IdealSheafData.ker_subschemeι _)
  exact h.flip.paste_vert (isPullback_baseChange N K₁.subtype)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.torsionLevel_extends_from_dense_open_normal : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  first | exact @GlobalTheory.exists_torsion_level_extend | exact GlobalTheory.exists_torsion_level_extend | (intros; apply GlobalTheory.exists_torsion_level_extend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameTheta

theorem isOpen_frames {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) : IsOpen (FD.GG Ψ G p) := by
  have hmat : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.mat x τ := fun τ =>
    show Continuous fun x : FD.Frame Ψ r => (x τ : Matrix (Fin r) (Fin r) ℂ) from continuous_apply τ
  have hgram : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.gram τ.1 G (FD.mat x τ) := by
    intro τ
    refine continuous_matrix fun a b => ?_
    simp only [FD.gram, FD.hermC, FD.col, FD.mat, Matrix.of_apply]
    fun_prop
  have hdmin : ∀ (τ : Ψ) (i : Fin (r + 1)), Continuous fun x : FD.Frame Ψ r => FD.dmin G x τ i := by
    intro τ i
    unfold FD.dmin FD.lminor
    exact ((hgram τ).matrix_submatrix _ _).matrix_det
  unfold FD.GG
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (hmat τ).matrix_det continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))

theorem exists_thetaFrame_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → IsPreconnected (FD.GG Ψ Gm (U.Di i).q) → ∀ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La), (∀ a b, (U.Di i).EF (bas a) (bas b) = -omegaStd a b) → ∀ (m : ℕ) (ι : (Fin m → ℂ) ≃L[ℂ] FD.Frame Ψ r), ∃ (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), (∀ b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q, IsUnit (h b).det ∧ (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef ∧ ∀ k, h b *ᵥ Pf (ι b) (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ Pf (ι b) (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1) ∧ (∀ j k, DifferentiableOn ℂ (fun b => h b j k) (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) ∧ DifferentiableOn ℂ (fun b => τ b j k) (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q)) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) (fun b => U.u i (Pf (ι b))) (fun b z => (U.ex i (Pf (ι b)) z).left) (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) := by
  classical
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hφ hr hPf hconn bas hbas m ι
  have hper := (GlobalTheory.FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ hr).2
  have hdiff := (GlobalTheory.per_move E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ).1 Pf hPf
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (U.Di i) g ty bas hbas
  have hhol : IsHolPeriods (U.Di i) ty (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) (fun b => Pf (ι b)) :=
    ⟨fun b hb => (hper _ hb).2 _ (hPf _), fun v =>
      (hdiff v).comp ι.differentiable.differentiableOn fun _ hb => hb⟩
  have hopen : IsOpen (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) := (isOpen_frames Ψ Gm _).preimage ι.continuous
  have hpre : IsPreconnected (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) :=
    ι.toHomeomorph.isPreconnected_preimage.2 hconn
  have hex : ∀ b : Fin m → ℂ, ∃ h τ : Matrix (Fin g) (Fin g) ℂ, b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q →
      IsUnit h.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ k,
        h *ᵥ Pf (ι b) (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
        h *ᵥ Pf (ι b) (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1 := by
    intro b
    by_cases hb : b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q
    · obtain ⟨h, τ, h1, h2, h3, h4, -⟩ := hR1 _ (hhol.1 b hb)
      exact ⟨h, τ, fun _ => ⟨h2, h3, h4, h1⟩⟩
    · exact ⟨0, 0, fun h => absurd h hb⟩
  choose h τ hhτ using hex
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := U.theta i m _ (fun b => Pf (ι b)) bas (-1) h τ hopen hpre hhol
    (fun a b => by rw [hbas]; simp) (fun b hb => ⟨(hhτ b hb).2.2.1, (hhτ b hb).2.2.2⟩)
  exact ⟨h, τ, c₁, c₂, hhτ, hR2 m _ _ h τ hhol fun b hb => (hhτ b hb).2.2.2, hc₁, hc₂, hθ⟩

end GlobalTheory.FrameTheta
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem periods_eq_frame_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ x ∈ FD.GG Ψ Gm (U.Di i).q, IsPeriod (U.Di i) ty (Pf x) ∧ U.u i (Pf x) ≫ Xo.s = spMap σ) ∧ ∀ P, IsPeriod (U.Di i) ty P → ∃ x ∈ FD.GG Ψ Gm (U.Di i).q, Pf x = P := by
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hφ hr hPf
  refine ⟨fun x hx => ?_, fun P hP => ?_⟩
  · have h := ((FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ
      hr).2 x hx).2 (Pf x) (hPf x)
    exact ⟨h, U.over_σ i _ h⟩
  · obtain ⟨x, hx, h⟩ := exists_frame_of_isPeriod E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos
      hφ hr P hP
    exact ⟨x, hx, AddMonoidHom.ext fun v => funext fun k => (hPf x v k).trans (h v k).symm⟩

end GlobalTheory
end
