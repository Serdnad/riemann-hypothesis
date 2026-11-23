module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle107
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle022
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicDiscAvoidingPole
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle112
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle113
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chart_points_over_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) :=
  @PositivityTheory.Xgn.lattice_chart_points

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dvr_model_of_number_field_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (v : HeightOneSpectrum (𝓞 F')) (π : F'), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → NormalCpt ξ → v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra O Ω) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (s : X' ⟶ Spec (CommRingCat.of O)) (g : X' ⟶ X) (ϖ : O), IsProper s ∧ Irreducible ϖ ∧ Function.Injective (algebraMap O Ω) ∧ ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ∧ ξ' ≫ g = ξ ∧ IsCptGen ξ' ∧ (∀ q' : X', genPt ξ' ⤳ q') ∧ algebraMap O Ω ϖ = ψ π ∧ (∀ a : Ω, a ∈ (algebraMap O Ω).range ↔ ∃ b : F', v.valuation F' b ≤ 1 ∧ ψ b = a) ∧ (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → ∃ p' : Cpt ξ', g p'.1 = p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | exact GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

section Local

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {F : Type} [Field F] [NumberField F]


omit [NumberField F] in
theorem int_mem_regAt (hN : NormalCpt ξ) (φ : F →+* Ω) (a : 𝓞 F) (q : Cpt ξ) : φ (a : F) ∈ regAt ξ q :=
  hN q _ ((map_isIntegral_int φ (RingOfIntegers.isIntegral_coe a)).tower_top)

theorem overInt_of_normalCpt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
    (ht : CoordTie ℤ ξ fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) (hN : NormalCpt ξ) (φ : F →+* Ω) :
    OverInt y φ := by
  refine ⟨fun k => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
    exact ⟨c k, fun h0 => hc.1 (Finset.prod_eq_zero (Finset.mem_univ k) h0)⟩
  · have hc' : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
    have h1 := (ht.ring c hc' (φ (a : F))).2 fun p _ => int_mem_regAt hN φ a p
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩

theorem cst_mem_regAt_of_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) (a : F) :
    φ a ∈ regAt ξ p := by
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hu := hp n hn
  have h1 : φ (n • a) ∈ regAt ξ p := int_mem_regAt hN φ (⟨n • a, hi⟩ : 𝓞 F) p
  have h2 : φ a = (algebraMap ℤ Ω n)⁻¹ * φ (n • a) := by
    rw [zsmul_eq_mul, map_mul, map_intCast, eq_intCast, inv_mul_cancel_left₀]
    simpa using hu.1
  rw [h2]
  exact mul_mem hu.2.2 h1

theorem exists_place_of_notMem_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∉ genFibre ℤ ξ) :
    ∃ v : HeightOneSpectrum (𝓞 F), ∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p := by
  have := Centre.Sep.isLocalRing_regAt ξ p
  let f : 𝓞 F →+* regAt ξ p :=
    (φ.comp (algebraMap (𝓞 F) F)).codRestrict (regAt ξ p) fun a => int_mem_regAt hN φ a p
  have hf : ∀ a : 𝓞 F, ((f a : regAt ξ p) : Ω) = φ (a : F) := fun _ => rfl
  have hmem : ∀ a : 𝓞 F, a ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ↔ ¬ unitAt ξ p (φ (a : F)) := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Centre.Sep.isUnit_regAt_iff, hf]
  obtain ⟨o, ho, hu⟩ : ∃ o : ℤ, o ≠ 0 ∧ ¬ unitAt ξ p (algebraMap ℤ Ω o) := by
    by_contra h
    push_neg at h
    exact hp h
  have hne : (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ≠ ⊥ := by
    intro hbot
    have h1 : (o : 𝓞 F) ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f := by
      rw [hmem]
      simpa using hu
    rw [hbot, Ideal.mem_bot] at h1
    exact ho (by exact_mod_cast h1)
  refine ⟨⟨_, inferInstance, hne⟩, fun a ha => ?_⟩
  obtain ⟨n, d, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hd : unitAt ξ p (φ ((d : 𝓞 F) : F)) := by
    by_contra h
    exact d.2 ((hmem _).2 h)
  have h2 : φ a = φ (n : F) * (φ ((d : 𝓞 F) : F))⁻¹ := by
    have e' : a * ((d : 𝓞 F) : F) = (n : F) := e
    rw [← e', map_mul, mul_inv_cancel_right₀ hd.1]
  rw [h2]
  exact mul_mem (int_mem_regAt hN φ n p) hd.2.2

end Local

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.pair_frames_on_set : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | exact GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff

theorem embedding_integers_and_different_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 :=
  @PositivityTheory.Xgn.sequence_differentials_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.CompanionTheory.Relay.dvr_point_analytic_disc : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W : X.Opens) (x : Cpt ξ) (N : X.Opens) (f : Ω), LocallyOfFiniteType s → IsCptGen ξ → genPt ξ ∈ W → x.1 ∉ W → x.1 ∈ N → IsDiscreteValuationRing (regAt ξ x) → f ∉ regAt ξ x → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin 1 → ℂ) → (Γ(X, V) →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), V ≤ N ∧ IsHolPts (ball 0 1) ψ ∧ (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ genPt ξ ⤳ centre (spMap (ψ z) ≫ hV.fromSpec)) ∧ ∀ z ∈ punct 1 1 1, ⊤ ≤ (spMap (ψ z) ≫ hV.fromSpec) ⁻¹ᵁ W ∧ ValAt ξ (spMap (ψ z) ≫ hV.fromSpec) f (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  first | exact @PositivityTheory.Xgn.exists_holomorphic_disc_avoiding_pole | exact PositivityTheory.Xgn.exists_holomorphic_disc_avoiding_pole
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_lie_metric_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re := by
  exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.holomorphic_affine_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hol_polydisc_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.hol_polydisc_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hol_polydisc_chart <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.TieOfOrigin

theorem sum_fundOnRoot {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {G : Type} [AddCommGroup G]
    (f : Ψ × Fin N → G) (a : Ψ × Fin N) :
    ∑ r, fundOnRoot a r • f r = -∑ k ∈ Finset.Iic a.2, f (a.1, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a.1]
  · rw [← Finset.sum_neg_distrib, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic a.2))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [fundOnRoot, Finset.mem_Iic.mp hk]
    · intro k _ hk
      have hk' : ¬ k ≤ a.2 := fun h => hk (Finset.mem_Iic.mpr h)
      simp [fundOnRoot, hk']
  · intro τ _ hτ
    simp [fundOnRoot, hτ]
  · simp

theorem log_combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((Top.combLine ℓ n).h z) = ∑ j, n j • Real.log ((ℓ j).h z) := by
  show Real.log (∏ j, (ℓ j).h z ^ n j) = _
  rw [Real.log_prod fun j _ => (zpow_pos ((ℓ j).pos z hz) _).ne']
  simp [Real.log_zpow]

theorem sum_rootOnFund {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (f g : Ψ × Fin N → ℝ)
    (h : ∀ a, g a = -∑ k ∈ Finset.Iic a.2, f (a.1, k)) (r : Ψ × Fin N) :
    ∑ a, rootOnFund r a • g a = f r := by
  have h1 : ∀ a, g a = ∑ r', fundOnRoot a r' • f r' := fun a => by rw [h, sum_fundOnRoot]
  simp only [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, (rootOnFund_mul_fundOnRoot_inverse Ψ N r _).1]
  simp

end GlobalTheory.CompanionTheory.Ar.TieOfOrigin

open GlobalTheory.CompanionTheory.Ar.TieOfOrigin in
theorem GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → AlgOver (Or.Re.comap some) → ∃ T : HodgeTie Y S (Module.finrank ℚ c.F) RM, T.A = Or.𝔐 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or hvb hdiscr halg
  refine ⟨{ A := Or.𝔐, Fl := Or.Fl, e := Or.e, roots := Or.lines, sing := Or.sing, sing_deg := Or.sing_deg
            hodge := Or.hodge, Sy := Sys.comap some, Re := Or.Re.comap some, alg := halg
            ref_deg := ?_, sing_eq := ?_, line_eq := ?_, δ_eq := Or.δ_eq, discr := hdiscr
            ht_vb := fun p hp s => (hvb p hp).2 s }, rfl⟩
  · rintro ⟨τ, i⟩
    refine (Or.fund_deg τ i).trans ?_
    refine Eq.trans ?_ (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => (Or.sing r).a) (τ, i)).symm
    simp only [Or.sing_deg]
  · rintro ⟨τ, i⟩ x hx
    have hz := (Or.Re.R.mem x x (Or.Re.R.mem_U x)).1
    refine (log_combLine _ _ _ hz).trans ?_
    refine (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x))) (τ, i)).trans ?_
    exact (Or.fund_sing τ i x hx).symm
  · have h0 : 0 < Sys.t₀ := (Sys.reg none).1
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht r z hz
    refine Real.log_injOn_pos ((RM.x t r).pos z hz.1) (HermLine.pos _ z hz.1) ?_
    refine Eq.trans ?_ (log_combLine _ _ _ hz.1).symm
    exact (@sum_rootOnFund _ _ (_) _ (fun r => Real.log ((RM.x t r).h z))
      (fun a => Real.log ((Or.Re.line (some a) t).h z))
      (fun a => Or.fund_reg a.1 a.2 t ht.1 ht.2 z hz) r).symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.small_points_coord_ratio_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∀ (i : J k₀) (k : K) (c : J k), z ⟨k₀, i⟩ ≠ 0 → z ⟨k, c⟩ ≠ 0 → ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ), (∀ j, (F j).IsHomogeneous n) ∧ (∀ j, MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F c) * y ⟨k, j⟩) ∧ MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F c) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms | exact GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_add_lattice_eq_of_isFn : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → ∀ (l : a.u.Λ) (w : Fin g → ℂ), θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | exact GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.nonzero_coords_of_nonzero_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.len σ x ^ 2 = Real.pi * (a.herm c c).re → x ≠ 0 → c ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero <;> assumption)
end
