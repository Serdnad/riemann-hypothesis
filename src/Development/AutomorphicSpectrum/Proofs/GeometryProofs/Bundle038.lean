module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RegSection

theorem section_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (s t : Γ(X, U))
    (e : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) =
      genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq t)) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => h.inj ⟨q, hU q hq⟩ (e q hq)

theorem existsUnique_section : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω), (U : Set X).Nonempty → (∀ q (hq : q ∈ U), a ∈ regAt ξ ⟨q, hU q hq⟩) → ∃! g : Γ(X, U), ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq g) = a := by
  intro X Ω _ ξ _ h U hU a _ ha
  have loc : ∀ x : U, ∃ (W : X.Opens) (_ : W ≤ U) (hx : x.1 ∈ W) (t : Γ(X, W)),
      genMap ξ ⟨x.1, hU x.1 x.2⟩ (X.presheaf.germ W x.1 hx t) = a := by
    intro x
    obtain ⟨g, hg⟩ := ha x.1 x.2
    obtain ⟨W, hx, t, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨W ⊓ U, inf_le_right, ⟨hx, x.2⟩, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
    exact (congrArg (genMap ξ ⟨x.1, hU x.1 x.2⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) x.1 ⟨hx, x.2⟩ t)).trans hg
  choose W hWU hx t ht using loc
  have val : ∀ (x : U) (y : X) (hy : y ∈ W x),
      genMap ξ ⟨y, hU y (hWU x hy)⟩ (X.presheaf.germ (W x) y hy (t x)) = a := fun x y hy =>
    (genMap_germ_eq_genMap_germ ξ (W x) ⟨y, hU y (hWU x hy)⟩ ⟨x.1, hU x.1 x.2⟩ hy (hx x) (t x)).trans (ht x)
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    apply h.inj ⟨y, hU y (hWU i hi)⟩
    exact (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i))).trans
      ((val i y hi).trans ((val j y hj).symm.trans
        (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j))).symm))
  have hcov : U ≤ iSup W := fun y hy =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i)) hcov t compat
  have spec : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) = a := by
    intro q hq
    have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hWU ⟨q, hq⟩)) q (hx ⟨q, hq⟩) s
    have e2 : (X.presheaf.map (homOfLE (hWU ⟨q, hq⟩)).op).hom s = t ⟨q, hq⟩ := hs ⟨q, hq⟩
    exact (congrArg (genMap ξ ⟨q, hU q hq⟩) e).symm.trans
      ((congrArg (fun z => genMap ξ ⟨q, hU q hq⟩ ((X.presheaf.germ (W ⟨q, hq⟩) q (hx ⟨q, hq⟩)).hom z)) e2).trans
        (ht ⟨q, hq⟩))
  exact ⟨s, spec, fun s' hs' => section_eq h U hU s' s fun q hq => (hs' q hq).trans (spec q hq).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RegSection
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFibre

variable {Y P : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isIso_stalkMap_of_lift (f : Y ⟶ P) [Mono f] (y : Y)
    (t : Spec (P.presheaf.stalk (f y)) ⟶ Y) (ht : t ≫ f = P.fromSpecStalk (f y)) :
    IsIso (f.stalkMap y) := by
  have h0 : Spec.map (f.stalkMap y) ≫ P.fromSpecStalk (f y) = Y.fromSpecStalk y ≫ f :=
    Scheme.SpecMap_stalkMap_fromSpecStalk f
  have h1 : Spec.map (f.stalkMap y) ≫ t = Y.fromSpecStalk y := by
    rw [← cancel_mono f, Category.assoc, ht, h0]
  have hc : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) = y := by
    have e1 : Spec.map (f.stalkMap y) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) =
        IsLocalRing.closedPoint (P.presheaf.stalk (f y)) := Spec_closedPoint
    have e2 : (Spec.map (f.stalkMap y) ≫ t) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y := by
      rw [h1]
      exact Scheme.fromSpecStalk_closedPoint
    rw [← e1]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2
  have hs : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) ⤳ y := by rw [hc]
  have h2 : Spec.map (Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t) ≫ Y.fromSpecStalk y = t := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  generalize Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t = τ at h2
  refine ⟨τ, ?_, ?_⟩
  · apply Spec.map_injective
    rw [← cancel_mono (P.fromSpecStalk (f y)), Spec.map_comp, Category.assoc, h0, ← Category.assoc, h2, ht,
      Spec.map_id, Category.id_comp]
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk y), Spec.map_comp, Category.assoc, h2, h1, Spec.map_id, Category.id_comp]

theorem genMap_bijective {ζ : Spec (CommRingCat.of Ω) ⟶ P} (h : IsCptGen ζ) (p : Cpt ζ) (e : p.1 = genPt ζ) :
    Function.Bijective (genMap ζ p) := by
  obtain ⟨p, hp⟩ := p
  obtain rfl : p = genPt ζ := e
  have : P.presheaf.stalkSpecializes hp = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, this]
  exact h.bij

theorem isCptGen_of_isIso_stalkMap (f : Y ⟶ P) (hf : ∀ y, IsIso (f.stalkMap y))
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have hd : Dominates ξ (ξ ≫ f) f (RingHom.id Ω) := by
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ ≫ f
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  have hb : ∀ q, Function.Bijective (f.stalkMap q).hom := fun q =>
    have := hf q
    ConcreteCategory.bijective_of_isIso (f.stalkMap q)
  have hcl : ∀ (q : Cpt ξ), genPt (ξ ≫ f) ⤳ f q.1 := fun q =>
    RegAtDom.map_genPt hd ▸ q.2.map f.continuous
  have hcomp : ∀ (q : Cpt ξ), genMap ξ q ∘ (f.stalkMap q.1).hom = genMap (ξ ≫ f) ⟨f q.1, hcl q⟩ := fun q =>
    funext fun t => RegAtDom.genMap_stalkMap hd q.1 q.2 (hcl q) t
  have hself : genMap ξ ⟨genPt ξ, specializes_rfl⟩ = (Scheme.stalkClosedPointTo ξ).hom := by
    have : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    have e : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫ Scheme.stalkClosedPointTo ξ =
        Scheme.stalkClosedPointTo ξ := by
      rw [this]
      exact Category.id_comp _
    exact congrArg (fun g => g.hom) e
  refine ⟨?_, fun q => ?_⟩
  · have e := hcomp ⟨genPt ξ, specializes_rfl⟩
    have hB := genMap_bijective h ⟨f (genPt ξ), hcl ⟨genPt ξ, specializes_rfl⟩⟩ (RegAtDom.map_genPt hd)
    rw [← e] at hB
    rw [← hself]
    exact ⟨hB.1.of_comp_right (hb _).2, hB.2.of_comp⟩
  · have hi := h.inj ⟨f q.1, hcl q⟩
    rw [← hcomp q] at hi
    exact hi.of_comp_right (hb _).2

variable {F : Type} [Field F] [NumberField F]


omit [NumberField F] in
theorem injective_of_charZero [CharZero Ω] (φ : 𝓞 F →+* Ω) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem exists_lift_field {R : CommRingCat.{0}} [IsLocalRing R] (g : Spec R ⟶ Sp (𝓞 F)) (z : Sp F)
    (hz : g (IsLocalRing.closedPoint R) = spMap (algebraMap (𝓞 F) F) z) :
    ∃ v : Spec R ⟶ Sp F, v ≫ spMap (algebraMap (𝓞 F) F) = g := by
  have hg : Spec.map (Spec.preimage g) = g := Spec.map_preimage g
  generalize Spec.preimage g = c at hg
  subst hg
  have hu : ∀ a : nonZeroDivisors (𝓞 F), IsUnit (c.hom a) := by
    intro a
    by_contra hn
    have h1 : (a : 𝓞 F) ∈ (Spec.map c (IsLocalRing.closedPoint R)).asIdeal :=
      (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [hz] at h1
    have h2 : algebraMap (𝓞 F) F a ∈ PrimeSpectrum.asIdeal z := h1
    have hp : (PrimeSpectrum.asIdeal z).IsPrime := PrimeSpectrum.isPrime _
    rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal z), Ideal.mem_bot] at h2
    have h3 : (a : 𝓞 F) = 0 := IsFractionRing.injective (𝓞 F) F (h2.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero a.2 h3
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors (𝓞 F)) (S := F) hu)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem isIso_stalkMap_fst (s : P ⟶ Sp (𝓞 F)) (y : ↑(pullback s (spMap (algebraMap (𝓞 F) F)))) :
    IsIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap y) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 F) F)) := IsLocalization.epi (nonZeroDivisors (𝓞 F)) F
  have : Mono (spMap (algebraMap (𝓞 F) F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hz : (P.fromSpecStalk (pullback.fst s (spMap (algebraMap (𝓞 F) F)) y) ≫ s) (IsLocalRing.closedPoint _) =
      spMap (algebraMap (𝓞 F) F) (pullback.snd s (spMap (algebraMap (𝓞 F) F)) y) := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    rw [Scheme.fromSpecStalk_closedPoint]
    have e : (pullback.fst s (spMap (algebraMap (𝓞 F) F)) ≫ s) y =
        (pullback.snd s (spMap (algebraMap (𝓞 F) F)) ≫ spMap (algebraMap (𝓞 F) F)) y := by
      rw [pullback.condition]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (e.trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨v, hv⟩ := exists_lift_field _ _ hz
  exact isIso_stalkMap_of_lift _ y (pullback.lift _ v hv.symm) (pullback.lift_fst _ _ _)

theorem exists_point : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P), IsCptGen ξ₀ → ∃ (b : F →+* Ω) (ξF : Sp Ω ⟶ pullback s (spMap (algebraMap (𝓞 F) F))), ξF ≫ pullback.fst _ _ = ξ₀ ∧ ξF ≫ pullback.snd _ _ = spMap b ∧ IsCptGen ξF := by
  intro F _ _ P s Ω _ _ ξ₀ h
  have hφ : Spec.map (Spec.preimage (ξ₀ ≫ s)) = ξ₀ ≫ s := Spec.map_preimage _
  generalize Spec.preimage (ξ₀ ≫ s) = φ at hφ
  have hinj : Function.Injective φ.hom := injective_of_charZero φ.hom
  have hb : (CommRingCat.ofHom (algebraMap (𝓞 F) F)) ≫ CommRingCat.ofHom (IsFractionRing.lift hinj) = φ := by
    ext a
    simp
  have hw : ξ₀ ≫ s = spMap (IsFractionRing.lift hinj) ≫ spMap (algebraMap (𝓞 F) F) :=
    hφ.symm.trans ((congrArg Spec.map hb.symm).trans (Spec.map_comp _ _))
  refine ⟨IsFractionRing.lift hinj, pullback.lift ξ₀ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  apply isCptGen_of_isIso_stalkMap (pullback.fst _ _) (isIso_stalkMap_fst s)
  rwa [pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames

theorem mem_prime_germ_eq_zero {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) (x : A)
    (hF : IsField (X.presheaf.stalk x.1)) (f : Γ(X, A)) (hf : f ∈ (hA.primeIdealOf x).asIdeal) :
    X.presheaf.germ A x.1 x.2 f = 0 := by
  have hl := hA.isLocalization_stalk x
  have h1 : algebraMap Γ(X, A) (X.presheaf.stalk x.1) f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x.1)
      (hA.primeIdealOf x).asIdeal f).2 hf
  have h2 : ¬ IsUnit (algebraMap Γ(X, A) (X.presheaf.stalk x.1) f) := h1
  by_contra h0
  exact h2 (by
    let _ := hF.toField
    exact IsUnit.mk0 _ h0)

theorem germ_injective {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) [IsDomain Γ(X, A)] (x : A) :
    Function.Injective (X.presheaf.germ A x.1 x.2) := by
  have hl := hA.isLocalization_stalk x
  exact IsLocalization.injective (X.presheaf.stalk x.1)
    (M := (hA.primeIdealOf x).asIdeal.primeCompl)
    ((hA.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors)

theorem genPt_specializes_of_isDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  intro X Ω _ ξ A hA p hgen hdom hp z hz
  have hx : genPt ξ ∈ A := p.2.mem_open A.2 hp
  let x : A := ⟨genPt ξ, hx⟩
  let q : A := ⟨p.1, hp⟩
  have hF : IsField (X.presheaf.stalk x.1) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hgen.bij).toMulEquiv
  have hbot : (hA.primeIdealOf x).asIdeal = ⊥ := by
    refine le_antisymm (fun f hf => ?_) bot_le
    have h0 := mem_prime_germ_eq_zero hA x hF f hf
    have h1 : X.presheaf.germ A p.1 hp f = 0 := by
      apply hgen.inj p
      have h2 : X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f) =
          X.presheaf.germ A (genPt ξ) hx f := by
        exact congr($(X.presheaf.germ_stalkSpecializes hp p.2).hom f)
      rw [map_zero]
      change (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f)) = 0
      rw [h2]
      have h3 : X.presheaf.germ A (genPt ξ) hx f = 0 := h0
      rw [h3]
      exact map_zero (Scheme.stalkClosedPointTo ξ).hom
    exact germ_injective hA q (h1.trans (map_zero _).symm)
  obtain ⟨t, rfl⟩ : z ∈ Set.range hA.fromSpec := by rwa [hA.range_fromSpec]
  have hs : hA.primeIdealOf x ⤳ t := by
    refine (PrimeSpectrum.le_iff_specializes (hA.primeIdealOf x) t).1 ?_
    change (hA.primeIdealOf x).asIdeal ≤ _
    rw [hbot]
    exact bot_le
  have := hs.map hA.fromSpec.continuous
  rwa [hA.fromSpec_primeIdealOf] at this

end GlobalTheory.CompanionTheory.Ar.LocFrames
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.tangent_section_additive : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U) (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U)
    (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)),
    ((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s =
      (v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SqAdd.tan_mul_add | exact GlobalTheory.CompanionTheory.Ar.SqAdd.tan_mul_add | (intros; apply GlobalTheory.CompanionTheory.Ar.SqAdd.tan_mul_add <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.generic_point_lift_along_iso : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W), IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) → ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameFibre

section Push

variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    have h1 := hφ.1.w
    have h2 := Over.w x
    simp only [Over.mk_hom, Category.assoc, Functor.id_obj, Functor.const_obj_obj, Over.mk_left]
    rw [h1, ← Category.assoc, h2])

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x y : T ⟶ G') :
    push hφ (x * y) = push hφ x * push hφ y := by
  apply Over.OverMorphism.ext
  exact (hφ.2 T x y (push hφ x) (push hφ y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) (T : Over S') :
    push hφ (1 : T ⟶ G') = 1 := by
  have h := push_mul hφ (1 : T ⟶ G') 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.mp h

end Push

theorem spec_fst_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [dualMap]

theorem spec_alg_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap f)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A))) =
      Spec.map (CommRingCat.ofHom (algebraMap B (DualNumber B))) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_epsMul_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : A) :
    Spec.map (CommRingCat.ofHom (epsMul (f c))) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap f)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  ext <;> simp [dualMap, epsMul, mul_comm]

theorem exists_linear_of_pullback {X : Scheme.{0}} {R : Type} [CommRing R] {G' : Over (Sp R)} [GrpObj G']
    {G : Over X} [GrpObj G] {h : Sp R ⟶ X} {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G h φ) {g : ℕ}
    (M : LieModel G' (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) {Vz : Type} [AddCommGroup Vz] [Module ℂ Vz]
    (MR : LieModel G (spMap ψ ≫ h) Vz) :
    ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R,
      (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ φ := by
  let c : epsAt (spMap ψ ≫ h) ⟶ Over.mk ((epsAt (𝟙 (Sp R))).hom ≫ h) :=
    Over.homMk (spMap (dualMap ψ)) (by
      have key := spec_alg_dualMap ψ
      simp only [Over.mk_hom, Category.comp_id]
      rw [← Category.assoc, key, Category.assoc])
  let w : (Fin g → R) → (epsAt (spMap ψ ≫ h) ⟶ G) := fun x => c ≫ push hφ (M.pt x)
  have wl : ∀ x, (w x).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ φ := fun _ => rfl
  have wt : ∀ x, IsTanAt G (spMap ψ ≫ h) (w x) := by
    intro x
    let c0 : Over.mk (spMap ψ ≫ h) ⟶ Over.mk ((Over.mk (𝟙 (Sp R))).hom ≫ h) :=
      Over.homMk (spMap ψ) (by simp)
    have h0 : c0 ≫ push hφ (1 : Over.mk (𝟙 (Sp R)) ⟶ G') = 1 := by
      rw [push_one]; exact MonObj.comp_one c0
    have h1 : spMap ψ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G').left ≫ φ = (1 : Over.mk (spMap ψ ≫ h) ⟶ G).left :=
      congrArg CommaMorphism.left h0
    have h2 := M.tan x
    unfold IsTanAt at h2 ⊢
    rw [wl, ← h1, ← h2, ← Category.assoc, spec_fst_dualMap ψ]
    simp only [Category.assoc]
  choose j hj using fun x => MR.onto (w x) (wt x)
  have jadd : ∀ x y, j (x + y) = j x + j y := by
    intro x y
    apply MR.inj
    rw [MR.add, hj, hj, hj]
    simp only [w, M.add, push_mul, MonObj.comp_mul]
  have jsmul : ∀ (a : R) x, j (a • x) = ψ a • j x := by
    intro a x
    apply MR.inj
    apply Over.OverMorphism.ext
    rw [MR.smul, hj, hj, wl, wl, M.smul, ← Category.assoc (Spec.map _) (spMap (dualMap ψ)),
      spec_epsMul_dualMap]
    simp only [Category.assoc]
  let J : (Fin g → R) →+ Vz := AddMonoidHom.mk' j jadd
  refine ⟨∑ i, (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ).smulRight (j (Pi.single i 1)), fun x => ?_⟩
  have hΘ : (∑ i, (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ).smulRight (j (Pi.single i 1)))
      (fun e => ψ (x e)) = j x := by
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin g → R) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    have hJ : J x = ∑ i, J (x i • (Pi.single i 1 : Fin g → R)) := by
      conv_lhs => rw [hx]
      exact map_sum J _ _
    have hJ' : j x = ∑ i, ψ (x i) • j (Pi.single i 1) := by
      refine hJ.trans (Finset.sum_congr rfl fun i _ => jsmul _ _)
    rw [hJ']
    simp [LinearMap.sum_apply]
  rw [hΘ, hj, wl]

theorem exists_linear_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (h : Sp R ⟶ X) (m : SABMap t' t h) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel t.G (spMap ψ ≫ h) Vz), ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R, (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ m.φ := by
  intro E _ _ _ H X t R _ t' h m g M ψ Vz _ _ MR
  exact exists_linear_of_pullback m.cart M ψ MR

end GlobalTheory.CompanionTheory.Ar.FrameFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabLie

theorem lieModel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (V : Type) [AddCommGroup V] [Module R V] (M : LieModel t'.G x V), ∃ Mf : LieModel t.G (x ≫ f) V, ∀ e, (Mf.pt e).left = (M.pt e).left ≫ m.φ := by
  intro E _ _ _ H S S' t' t f m R _ x V _ _ M
  obtain ⟨Mf, h⟩ := (LiePull.lieModel_pullback S S' t.G t'.G f m.φ m.cart R x V).2 M
  exact ⟨Mf, fun e => (h e).symm⟩

end GlobalTheory.CompanionTheory.Ar.SabLie
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem hodgeTate_endo : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) :=
  @PositivityTheory.HtPt.Htat.ht_olin

end GlobalTheory.CompanionTheory.Ar.BT
end
