module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymDivisible
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Basic.Complex.Basic
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle017
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle019
public import Mathlib.Algebra.Field.Subfield.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPrimes

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : X.Opens) (hg : genPt ξ ∈ V) : Γ(X, V) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ V (genPt ξ) hg).hom

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq (V : X.Opens) (hg : genPt ξ ∈ V) (p : Cpt ξ) (hp : p.1 ∈ V) (f : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) = secVal ξ V hg f := by
  change _ = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg f)
  rw [← X.presheaf.germ_stalkSpecializes hp p.2]
  rfl

theorem isUnit_iff_unitAt (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p))
    (s : X.presheaf.stalk p.1) : IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro h
    have h1 : IsUnit (genMap ξ p s) := h.map (genMap ξ p)
    refine ⟨h1.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := h
    refine ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ), ?_⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    simp
  · rintro ⟨h0, -, ⟨w, hw⟩⟩
    refine IsUnit.of_mul_eq_one w (hinj ?_)
    rw [map_mul, hw, map_one]
    exact mul_inv_cancel₀ h0

theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec y ∈ U := by
  change hU.fromSpec y ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨y, rfl⟩

theorem exists_secVal_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genPt ξ ∈ U)
    (hs : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → a ∈ regAt ξ ⟨q, h⟩) :
    ∃ f : Γ(X, U), secVal ξ U hg f = a := by
  let ρ := secVal ξ U hg
  let I : Ideal Γ(X, U) :=
    { carrier := {r | ∃ f, ρ f = ρ r * a}
      add_mem' := by
        rintro r s ⟨f, hf⟩ ⟨g, hg⟩
        exact ⟨f + g, by rw [map_add (f := _), map_add (f := _), hf, hg, add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r s ⟨f, hf⟩
        exact ⟨r * f, by rw [smul_eq_mul, map_mul, map_mul, hf, _root_.mul_assoc]⟩ }
  by_cases hI : I = ⊤
  · obtain ⟨f, hf⟩ : (1 : Γ(X, U)) ∈ I := hI ▸ Submodule.mem_top
    exact ⟨f, by rw [hf, map_one, _root_.one_mul]⟩
  · exfalso
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    let q : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
    have hq : hU.fromSpec q ∈ U := fromSpec_mem hU q
    have hsp := hs _ hq
    obtain ⟨σ, hσ⟩ := ha _ hsp hq
    have hloc := hU.isLocalization_stalk' q hq
    obtain ⟨⟨r, s⟩, e⟩ := @IsLocalization.surj _ _ _ _ _
      (X.presheaf.algebra_section_stalk ⟨hU.fromSpec q, hq⟩) hloc σ
    have e' : σ * X.presheaf.germ U _ hq s.1 = X.presheaf.germ U _ hq r := e
    have e2 := congrArg (genMap ξ ⟨_, hsp⟩) e'
    rw [map_mul, hσ, genMap_germ_eq U hg ⟨_, hsp⟩ hq s.1, genMap_germ_eq U hg ⟨_, hsp⟩ hq r] at e2
    exact s.2 (hIm ⟨r, by rw [← e2, mul_comm]⟩)

theorem notMem_iff_isUnit_germ {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (hq : hU.fromSpec y ∈ U) (f : Γ(X, U)) :
    f ∉ y.asIdeal ↔ IsUnit (X.presheaf.germ U (hU.fromSpec y) hq f) := by
  rw [← X.mem_basicOpen f _ hq, ← PrimeSpectrum.mem_basicOpen]
  have h := hU.fromSpec_preimage_basicOpen f
  change _ ↔ y ∈ (hU.fromSpec ⁻¹ᵁ X.basicOpen f)
  rw [h]
  rfl

theorem inChart_genPt (hξ : IsCptGen ξ) {κ : Type} (x : κ → Ω) (c : κ) (hc : x c ≠ 0) :
    InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ := by
  refine ⟨hc, fun j => ?_⟩
  obtain ⟨s, hs⟩ := hξ.bij.2 (x j / x c)
  refine ⟨s, ?_⟩
  rw [← hs]
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

end GlobalTheory.CompanionTheory.Ar.ChartPrimes

namespace GlobalTheory.CompanionTheory.Ar


open ChartPrimes in
theorem chart_point_of_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type)
    [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ), x c ≠ 0 →
    ∀ I : Ideal (Algebra.adjoin o (Set.range fun j => x j / x c)), I.IsPrime →
    ∃! p : Cpt ξ, InChart ξ x c p ∧ ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ I ↔ unitAt ξ p (s : Ω) := by
  intro X Ω _ ξ o _ _ κ x T c hc I hI
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hs : ∀ q ∈ U, genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h, -⟩ := (hmem q).1 hq
    exact h
  have hin : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → InChart ξ x c ⟨q, h⟩ := fun q h hq => by
    obtain ⟨_, h'⟩ := (hmem q).1 hq
    exact h'
  let ρ := secVal ξ U hg
  have hρA : ∀ f, ρ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun f =>
    (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq U hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩
  have hsurj : ∀ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c), ∃ f, ρ f = a := fun a ha =>
    exists_secVal_eq hU hg hs a fun q h hq => (T.ring c hc a).1 ha _ (hin q h hq)
  let ρ' : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) := ρ.codRestrict _ hρA
  have hρ' : ∀ f, ((ρ' f : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = ρ f := fun _ => rfl

  have key : ∀ (y : PrimeSpectrum Γ(X, U)) (h : genPt ξ ⤳ hU.fromSpec y) (f : Γ(X, U)),
      f ∉ y.asIdeal ↔ unitAt ξ ⟨hU.fromSpec y, h⟩ (ρ f) := fun y h f => by
    have hq := fromSpec_mem hU y
    rw [notMem_iff_isUnit_germ hU y hq f, ← genMap_germ_eq U hg ⟨_, h⟩ hq f]
    exact isUnit_iff_unitAt ⟨_, h⟩ (T.gen.inj _) _
  let y : PrimeSpectrum Γ(X, U) := ⟨I.comap ρ', inferInstance⟩
  have hy := fromSpec_mem hU y
  refine ⟨⟨hU.fromSpec y, hs _ hy⟩, ⟨hin _ _ hy, fun s => ?_⟩, ?_⟩
  · obtain ⟨f, hf⟩ := hsurj s s.2
    have hfs : ρ' f = s := Subtype.ext hf
    have := key y (hs _ hy) f
    rw [hf] at this
    rw [← this, ← hfs]
    rfl
  · rintro ⟨p, hp⟩ ⟨hpc, hpI⟩
    have hpU : p ∈ U := (hmem p).2 ⟨hp, hpc⟩
    obtain ⟨y', rfl⟩ : ∃ y', hU.fromSpec y' = p := ⟨_, hU.fromSpec_primeIdealOf ⟨p, hpU⟩⟩
    have hyy : y' = y := PrimeSpectrum.ext (Ideal.ext fun f => not_iff_not.1 ((key y' hp f).trans (hpI (ρ' f)).symm))
    exact Subtype.ext (congrArg (fun t => hU.fromSpec t) hyy)

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordsDown

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isUnit_natCast_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (r : ℕ) (hr : r.Prime) :
    IsUnit (r : A) := by
  apply isUnit_of_map_unit φ
  rw [map_natCast]
  exact isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hr.ne_zero)

theorem unitAt_centre {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h : genPt ξ' ⤳ centre z) (r : ℕ) (hr : r.Prime) : unitAt ξ' ⟨centre z, h⟩ (r : Ω) := by
  have hz : IsLocalHom (Scheme.stalkClosedPointTo z).hom := inferInstance
  have hu : IsUnit ((r : X'.presheaf.stalk (centre z))) := isUnit_natCast_of_local (Scheme.stalkClosedPointTo z).hom r hr
  have hu' : IsUnit ((r : Ω)) := by
    have := hu.map (genMap ξ' ⟨centre z, h⟩)
    rwa [map_natCast] at this
  obtain ⟨u, hu1⟩ := hu.exists_right_inv
  refine ⟨hu'.ne_zero, ⟨(r : X'.presheaf.stalk (centre z)), map_natCast _ _⟩, ⟨u, ?_⟩⟩
  have e := congrArg (genMap ξ' ⟨centre z, h⟩) hu1
  rw [map_mul, map_natCast, map_one] at e
  exact eq_inv_of_mul_eq_one_right e

theorem genMap_stalkMap (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem valAt_down {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (g : X' ⟶ X) (hinj : IsCptGen ξ')
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (h' : genPt ξ' ⤳ centre z)
    (h : genPt (ξ' ≫ g) ⤳ g (centre z))
    (hreg : regAt ξ' ⟨centre z, h'⟩ = regAt (ξ' ≫ g) ⟨g (centre z), h⟩)
    {a : Ω} {r : ℂ} (hv : ValAt ξ' z a r) : ValAt (ξ' ≫ g) (z ≫ g) a r := by
  obtain ⟨h1, s, hs, rfl⟩ := hv
  have ha : a ∈ regAt (ξ' ≫ g) ⟨g (centre z), h⟩ := by
    rw [← hreg]
    exact ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := ha
  have e : (g.stalkMap (centre z)).hom s₀ = s := by
    apply hinj.inj ⟨centre z, h'⟩
    rw [genMap_stalkMap ξ' g ⟨centre z, h'⟩ h s₀]
    exact hs₀.trans hs.symm
  subst e
  refine ⟨h, s₀, hs₀, ?_⟩
  exact congrArg (fun t => t.hom s₀) (Scheme.stalkClosedPointTo_comp z g)

theorem coordsAt_down : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (K' : Type) (J' : K' → Type) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, J' k) → ℂ), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → IsCptGen ξ' → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → CoordsAt ξ' y' z w → CoordsAt ξ y (z ≫ g) (fun p : (Σ k, J k) => w ⟨bk p.1, bx p.1 p.2⟩) := by
  intro X X' Ω _ ξ ξ' g K J y K' J' y' bk bx z w hall hall' hgen hcomp hy hreg hw
  subst hcomp
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := hw.1 (bk k)
    exact ⟨(bx k).symm c, by simpa using hc⟩
  · obtain ⟨hne, hv⟩ := hw.2 (bk k) (bx k c) hc
    refine ⟨by rwa [hy] at hne, fun i => ?_⟩
    obtain ⟨r, hr, e⟩ := hv (bx k i)
    rw [hy, hy] at hr
    have h' := hall' (centre z)
    have h := hall (g (centre z))
    refine ⟨r, valAt_down g hgen z h' h (hreg ⟨centre z, h'⟩ (fun p hp hf => hf (unitAt_centre z h' p hp)) h) hr, e⟩

end GlobalTheory.CompanionTheory.Ar.CoordsDown
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem antisymPerturbation_holds : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement :=
  GroundTheory.Heights₂.Heights.AntisymPerturbation.proof
    (GroundTheory.Heights₂.Heights.AntisymStability.proof
      GroundTheory.Heights₂.Heights.AntisymDivisible.proof)

end GlobalTheory.CompanionTheory.Ar.Link
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.antisymmetric_perturbation_holds : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement := by
  exact GroundTheory.Heights₂.Heights.AntisymPerturbation.proof
    (GroundTheory.Heights₂.Heights.AntisymStability.proof
      GroundTheory.Heights₂.Heights.AntisymDivisible.proof)
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.TwistLine

theorem forms_off_vanishing_locus : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 :=
  @PositivityTheory.Xgn.multihomogeneous_nonvanishing_off

end GlobalTheory.CompanionTheory.Ggeo.TwistLine
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.TwistLine

theorem finite_pairs_common_bidegree : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) :=
  @PositivityTheory.Xgn.multihomogeneous_twist_finite

end GlobalTheory.CompanionTheory.Ar.TwistLine
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.CompMem

theorem blockWeight_weight_apply {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  · intro b _ hb
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_eq_of_ne hb.symm]
  · simp

theorem comp_mem : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  intro K _ _ ι _ P hP f hf b
  obtain ⟨S, hS, rfl⟩ := hP
  classical
  letI := weightedGradedAlgebra ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι)
  refine weightedHomogeneousComponent_mem_of_mem ℤ _ ?_ hf b
  refine Ideal.homogeneous_span _ S fun g hg => ?_
  obtain ⟨a, ha⟩ := hS g hg
  refine ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 fun m hm => ?_⟩
  funext k
  rw [blockWeight_weight_apply]
  exact ha m (mem_support_iff.2 hm) k

end GlobalTheory.CompanionTheory.Ggeo.CompMem
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.different_ideal_local_generator : ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [CharZero Ω] (R : Subring Ω) [IsLocalRing R] (σ : 𝓞 F →+* Ω), (∀ a, σ a ∈ R) → ∃ d₀ ∈ differentIdeal ℤ (𝓞 F), σ d₀ ≠ 0 ∧ ∀ d ∈ differentIdeal ℤ (𝓞 F), σ d / σ d₀ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring | exact GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring | (intros; apply GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring <;> assumption)
end

section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Different

theorem padicValInt_discr_mul_count_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)),
      P.IsPrime → (p : 𝓞 E) ∈ P →
      ((padicValInt p (discr E) : ℕ)) * (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P =
        (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E := by
  intro E _ _ _ p hp P hP hpP
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hdecomp : (discr E).natAbs =
      p ^ padicValNat p (discr E).natAbs * ((discr E).natAbs / p ^ (discr E).natAbs.factorization p) := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (discr E).natAbs p]
    rw [Nat.factorization_def _ hp.out, Nat.padicValNat_def]
  have hnd : ¬ p ∣ (discr E).natAbs / p ^ (discr E).natAbs.factorization p :=
    Nat.not_dvd_ordCompl hp.out hd
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p _ _ hp.out hnd hdecomp P hP hpP
  rw [h]
  rw [padicValInt, Nat.padicValNat_def]

end GlobalTheory.CompanionTheory.Different
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.weil_pairing_transport_relation : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (C A : Type) [CommGroup C] [CommGroup A] (rel : A → C → Prop) (n : ℕ), 1 ≤ n →
  (∀ c : C, c ^ n = 1 → ∃ a : A, a ^ n = 1 ∧ rel a c) →
  (∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c) →
  (∀ a a' c c', rel a c → rel a' c' → rel (a * a') (c * c')) →
  (∀ a a' c, rel a c → rel a' c → a = a') →
  (∀ a c c', rel a c → rel a c' → c = c') →
  ∀ (e : C → C → Ωˣ) (e' : A → A → Ω'ˣ),
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g') →
  (∀ χ : C → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g) →
  (∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1) →
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e' x (g * g') = e' x g * e' x g') →
  (∀ χ : A → Ω'ˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e' x g) →
  (∀ y' : A, y' ^ n = 1 → ∃ y : C, y ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) ∧
  (∀ y : C, y ^ n = 1 → ∃ y' : A, y' ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorsionChars.chars_descend | exact GlobalTheory.CompanionTheory.Ar.TorsionChars.chars_descend | (intros; apply GlobalTheory.CompanionTheory.Ar.TorsionChars.chars_descend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.epi_ring_hom_field_closure : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top | exact GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top | (intros; apply GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.extend_to_fraction_field : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay | exact GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay | (intros; apply GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay <;> assumption)
end
