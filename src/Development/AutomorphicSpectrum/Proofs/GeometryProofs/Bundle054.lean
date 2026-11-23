module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle012
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle040
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanMul

abbrev red (C : Type) [CommRing C] : Sp C ⟶ Sp (DualNumber C) :=
  spMap (TrivSqZeroExt.fstHom C C C).toRingHom

theorem red_surj (C : Type) [CommRing C] (p : Sp (DualNumber C)) : ∃ q : Sp C, red C q = p := by
  let P : PrimeSpectrum (DualNumber C) := p
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ P.asIdeal := by
    intro a ha
    have h0 : a.fst = 0 := ha
    have h2 : a * a = 0 := by
      ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    have : a * a ∈ P.asIdeal := by rw [h2]; exact zero_mem _
    rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  haveI := P.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  refine ⟨(⟨_, hprime⟩ : PrimeSpectrum C), ?_⟩
  have e : PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom ⟨_, hprime⟩ = P := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom P.asIdeal) = P.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  exact e

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)


include hU in
theorem top_le {C : Type} [CommRing C] (t : Sp (DualNumber C) ⟶ X) (u : Γ(X, U) →+* C)
    (h : red C ≫ t = spMap u ≫ hU.fromSpec) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := red_surj C p
  show t (red C q) ∈ U
  have e : t (red C q) = hU.fromSpec (spMap u q) := by
    have := congrArg (fun f : Sp C ⟶ X => f q) h
    simpa using this
  rw [e]
  exact hU.range_fromSpec.subset (Set.mem_range_self _)

def ringOf {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem ringOf_spec {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) :
    spMap (ringOf t h) ≫ hU.fromSpec = t := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec t hU (isAffineOpen_top (Spec (CommRingCat.of A))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : spMap (ringOf t h) = Spec.map (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) := by
    unfold ringOf spMap
    rw [CommRingCat.ofHom_hom]
  rw [e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

include hU in
theorem ring_inj {A : Type} [CommRing A] {f g : Γ(X, U) →+* A}
    (h : spMap f ≫ hU.fromSpec = spMap g ≫ hU.fromSpec) : f = g := by
  rw [cancel_mono] at h
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

theorem ringOf_eq {A : Type} [CommRing A] {t : Sp A ⟶ X} (h : ⊤ ≤ t ⁻¹ᵁ U) {f : Γ(X, U) →+* A}
    (e : t = spMap f ≫ hU.fromSpec) : ringOf t h = f :=
  ring_inj hU ((ringOf_spec hU t h).trans e)

variable {S : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ S)

def redO : Over.mk y ⟶ epsAt y :=
  Over.homMk (red C) (by
    have h : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C := by
      ext a; simp
    show red C ≫ spMap (algebraMap C (DualNumber C)) ≫ y = y
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    simp)

def projO : epsAt y ⟶ Over.mk y :=
  Over.homMk (spMap (algebraMap C (DualNumber C))) rfl

theorem comp_one_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_mul_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) (a b : T ⟶ G) :
    f ≫ (a * b) = (f ≫ a) * (f ≫ b) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have rv : redO y ≫ v = 1 := Over.OverMorphism.ext hv
  have rw' : redO y ≫ w = 1 := Over.OverMorphism.ext hw
  have rvw : redO y ≫ (v * w) = 1 := by rw [comp_mul_O, rv, rw', _root_.one_mul]
  have r1 : redO y ≫ (1 : epsAt y ⟶ G) = 1 := comp_one_O _
  have lv : red C ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans hu
  have lw : red C ≫ w.left = spMap u ≫ hU.fromSpec := hw.trans hu
  have lvw : red C ≫ (v * w).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) rvw).trans hu
  have l1 : red C ≫ (1 : epsAt y ⟶ G).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) r1).trans hu
  have hv' := top_le hU _ u lv
  have hw' := top_le hU _ u lw
  have hvw := top_le hU _ u lvw
  have h1 := top_le hU _ u l1
  have e1 : (1 : epsAt y ⟶ G).left = spMap ((algebraMap C (DualNumber C)).comp u) ≫ hU.fromSpec := by
    have p1 : projO y ≫ (1 : Over.mk y ⟶ G) = 1 := comp_one_O _
    have p2 : spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left = (1 : epsAt y ⟶ G).left :=
      congrArg (fun f => CommaMorphism.left f) p1
    rw [← p2, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw) = u := by
    apply ring_inj hU
    have : spMap ((TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw)) =
        red C ≫ spMap (ringOf (v * w).left hvw) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc, ringOf_spec hU, lvw]
  have hχ' : ringOf (v * w).left hvw = χ := by
    ext s
    · rw [hχ]
      exact RingHom.congr_fun hfst s
    · have key := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom
        (GlobalTheory.T.tangent_section_additive S G C y v w hv hw U hv' hw' hvw h1 s)
      rw [map_add (f := _), map_add (f := _)] at key
      change ringOf (v * w).left hvw s + ringOf (1 : epsAt y ⟶ G).left h1 s =
        ringOf v.left hv' s + ringOf w.left hw' s at key
      rw [ringOf_eq hU h1 e1, ringOf_eq hU hv' ev, ringOf_eq hU hw' ew] at key
      have := congrArg TrivSqZeroExt.snd key
      have h0 : TrivSqZeroExt.snd (((algebraMap C (DualNumber C)).comp u) s) = 0 := by
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, h0, add_zero] at this
      rw [hs, this]
  rw [← hχ', ringOf_spec hU]

end GlobalTheory.CompanionTheory.Ar.TanMul
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.affine_domain_generic_specializes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | exact GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

theorem _root_.GlobalTheory.T.value_along_stalk_surjection : ∀ (X₀ X' : Scheme.{0}) (Ω R : Type) [Field Ω] [CommRing R] [IsLocalRing R] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R), ξ' ≫ π = ξ → Function.Surjective (π.stalkMap (centre z)).hom → ValAt ξ' z a r → ValAt ξ (z ≫ π) a r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective | exact GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.value_locally_regular_function : ∀ (X T : Scheme.{0}) (j : T ⟶ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (y₀ : Sp ℂ ⟶ T) (t : Ω) (r₀ : ℂ), ValAt ξ (y₀ ≫ j) t r₀ → ∃ W₁ : T.Opens, ⊤ ≤ y₀ ⁻¹ᵁ W₁ ∧ ∀ (V : T.Opens) (hV : IsAffineOpen V), V ≤ W₁ → ∃ g : Γ(T, V), ∀ (χ : Γ(T, V) →+* ℂ) (r : ℂ), ValAt ξ ((spMap χ ≫ hV.fromSpec) ≫ j) t r → r = χ g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SectionNear.section_near | exact GlobalTheory.CompanionTheory.Ar.SectionNear.section_near | (intros; apply GlobalTheory.CompanionTheory.Ar.SectionNear.section_near <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

theorem _root_.GlobalTheory.T.bt_order_value_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb | exact GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.every_component_in_some_chart : ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.lie_model_pullback_action_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X)
    (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω' V')
    (j : V →+ V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) →
    ∀ a e, j (ρ a e) = ρ' a (j e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | exact GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_vector_bundle_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E' : Type) [AddCommGroup E'] [Module Ω' E'] (j : E →+ E') (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E), Dominates ξ' ξ f i → (∀ (a : Ω) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → E), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) → L.IsVBOn T r V → (L.pull ξ' f j).IsVBOn {p' | ∃ h : genPt ξ ⤳ f p'.1, (⟨f p'.1, h⟩ : Cpt ξ) ∈ T} r (Submodule.span Ω' (j '' V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull | exact GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.frame_near_generic_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) (b : Fin r → E), IsCptGen ξ → (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) ∈ T → L.IsVBOn T r V → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = V → ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q ∈ T, q.1 ∈ W → L.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem Lat.pull_isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E E' : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω' E'] (j : E →+ E'), Dominates ξ' ξ f i → (∀ (a : Ω) (e : E), j (a • e) = i a • j e) → ∀ (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), LinearIndependent Ω' (fun k => j (b k)) → L.IsFrameAt b ⟨f p'.1, h⟩ → (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) p' := by
  intro X Ω _ ξ X' Ω' _ ξ' f i E E' _ _ _ _ j hD hj L r b p' h hli hb
  obtain ⟨h', hreg, -⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  refine ⟨hli, ?_⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := hb.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := by
      rw [← hL]; exact he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => ⟨i (c k), hreg _ (c k).2⟩, ?_⟩

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (hj (c k) (b k)).symm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨b k, ?_, rfl⟩
    show b k ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set E)
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem dominates_localRings : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) :=
  PositivityTheory.HtPt.Mb.dom_local

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.lattice_eq_of_codim_one_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (T : Set (Cpt ξ)), (∀ p ∈ T, ∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p ∈ T, IsIntegrallyClosed (X.presheaf.stalk p.1)) → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (L L' : Lat ξ E) (r : ℕ) (V : Submodule Ω E), L.IsVBOn T r V → L'.IsVBOn T r V → (∀ p ∈ T, ringKrullDim (X.presheaf.stalk p.1) = 1 → L p = L' p) → ∀ p ∈ T, L p = L' p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lat_agree_of_height_one | exact GlobalTheory.CompanionTheory.Ar.lat_agree_of_height_one | (intros; apply GlobalTheory.CompanionTheory.Ar.lat_agree_of_height_one <;> assumption)
end
