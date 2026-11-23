module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle088
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyOfHoms
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem iotaMulti_ne_zero_of_linearIndependent {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}
    {b : Fin r → V} (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin r)).toOrderEmbedding)
  intro h0
  apply h
  simpa [exteriorPower.ιMulti_family] using h0

theorem exists_unit_of_span_eq {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W] (R : Subring Ω) {c m : W}
    (hm : m ≠ 0) (h : Submodule.span R {c} = Submodule.span R {m}) :
    ∃ u : Ω, u ≠ 0 ∧ u ∈ R ∧ u⁻¹ ∈ R ∧ c = u • m := by
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self (R := R) c)
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 (h.symm ▸ Submodule.mem_span_singleton_self (R := R) m)
  have hu' : (u : Ω) • m = c := hu
  have hv' : (v : Ω) • c = m := hv
  have h1 : ((v : Ω) * u - 1) • m = 0 := by
    rw [sub_smul, mul_smul, hu', hv', one_smul, sub_self]
  have h2 : (v : Ω) * u = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hm)
  have h3 : (u : Ω) ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine ⟨u, h3, u.2, ?_, hu'.symm⟩
  rw [inv_eq_of_mul_eq_one_left h2]
  exact v.2

theorem exists_coeff_regular_of_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (b₁ : Fin p → V) (b₂ : Fin q → V), IsCoeffAt A B p q a b x 1 → A.IsFrameAt b₁ x → B.IsFrameAt b₂ x → ∃ α κ : Ω, a = α • exteriorPower.ιMulti Ω p b₁ ∧ b = κ • exteriorPower.ιMulti Ω q b₂ ∧ α / κ ∈ regAt ξ x := by
  intro X Ω _ ξ V _ _ A B p q a b x b₁ b₂ hc f₁ f₂
  obtain ⟨α₀, β₀, hα, hβ, hA, hB, h1⟩ := hc
  rw [one_mul] at h1
  subst h1
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₁] at hA
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₂] at hB
  obtain ⟨u, -, hu, -, hau⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₁.1) hA.symm
  obtain ⟨t, ht0, -, hti, hbt⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₂.1) hB.symm
  refine ⟨u / α₀, t / α₀, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, mul_smul, ← hau, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · rw [div_eq_inv_mul, mul_smul, ← hbt, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · have : u / α₀ / (t / α₀) = u * t⁻¹ := by field_simp
    rw [this]
    exact mul_mem hu hti

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis

theorem flagStep_full {E : Type} [AddCommGroup E] (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b : Fin r → E) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep
  have : {k : Fin r | (k : ℕ) < r} = Set.univ := by ext k; simp [k.2]
  rw [this, Set.image_univ]

theorem flag_b_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (t : CMType H ⊕ CMType H),
    LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 Fl t
  letI := 𝔐.fn.toAlgebra
  obtain ⟨cc, u, hc, _hj, _hjc, hb, _hu1, _hu0, hflag, _⟩ := Fl.generic
  refine ⟨hb t, ?_⟩
  have hle : Submodule.span Ω (Set.range (Fl.b t)) ≤ 𝔐.Vgen t := by
    rw [← flagStep_full, hflag t (labelRk D t), flagStep_full, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    exact (Fl.V₀_mem t (cc t l)).1 ((hc t).2 ▸ Submodule.subset_span ⟨l, rfl⟩)
  obtain ⟨U, hpU, b', hspan, hfr⟩ := 𝔐.vb t ⟨GlobalTheory.CompanionTheory.Ar.genPt 𝔐.ξ, 𝔐.all _⟩ trivial
  have hli' : LinearIndependent Ω b' := (hfr _ trivial hpU).1
  have hV : Submodule.span Ω (Set.range b') = 𝔐.Vgen t := hspan
  haveI : FiniteDimensional Ω (𝔐.Vgen t) := by
    rw [← hV]; exact FiniteDimensional.span_of_finite Ω (Set.finite_range b')
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← hV, finrank_span_eq_card (hb t), finrank_span_eq_card hli']

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.period_holomorphic_continuation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsOpen B → ∀ b₀ ∈ B, ∀ x ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = x ∧ ∀ b ∈ ball b₀ ε, s b ∈ e.per b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.per_spreads | exact GlobalTheory.CompanionTheory.Ar.Flat.per_spreads | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.per_spreads <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.period_lattice_discrete_free : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), ∀ b ∈ B, ∃ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b ∧ DiscreteTopology Γ₀ ∧ Module.Finite ℤ Γ₀ ∧ Module.Free ℤ Γ₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FamExp.per_discrete | exact GlobalTheory.CompanionTheory.Ar.Flat.FamExp.per_discrete | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FamExp.per_discrete <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.abelian_part_factors_through : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (K : Type) [Field K] (z : Sp K ⟶ S') (P : AbPart t (z ≫ f)), ∃ m' : SABMap P.tK t' z, m'.φ ≫ m.φ = P.m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK | exact GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_constants_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point | exact GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.abelian_part_maps_compatible_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left)) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, ((Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t'.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt e).left)) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanCompare.tan_compare | exact GlobalTheory.CompanionTheory.Ar.TanCompare.tan_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.TanCompare.tan_compare <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_component_base_change_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (a : Ω) (r : ℂ), ValAt 𝔐.ξ z₁ a r → ∃ h : a ∈ W, φ ⟨a, h⟩ = r) → (∀ (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ z₂ a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) → ∃ (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) ∧ (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) ∧ (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) ∧ (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) ∧ spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.exists_common_point | exact GlobalTheory.CompanionTheory.Ar.OrArch.exists_common_point | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.exists_common_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.holomorphic_family_of_homs : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D k A] (σ : k →+* ℂ) (ψ₀ : A →+* ℂ), ψ₀.comp (algebraMap k A) = σ → ∃ Ψ : (Fin D → ℂ) → (A →+* ℂ), IsHolPts (ball 0 1) Ψ ∧ Ψ 0 = ψ₀ ∧ (∀ z ∈ ball (0 : Fin D → ℂ) 1, (Ψ z).comp (algebraMap k A) = σ) ∧ ∀ a : A, (∀ z ∈ ball (0 : Fin D → ℂ) 1, Ψ z a = 0) → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ChartRing.exists_polydisc_chart | exact GlobalTheory.CompanionTheory.ChartRing.exists_polydisc_chart | (intros; apply GlobalTheory.CompanionTheory.ChartRing.exists_polydisc_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem not_inFibre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) {r : ℕ} (hr : r.Prime) :
    ¬ InFibre ξ r ⟨centre z, h⟩ := by
  intro hf
  apply hf
  have hs : genMap ξ ⟨centre z, h⟩ (r : X.presheaf.stalk (centre z)) = (r : Ω) := map_natCast _ r
  have hz : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
  have hu : IsUnit (r : X.presheaf.stalk (centre z)) := CxVal.isUnit _ (by
    rw [hz]; exact_mod_cast hr.ne_zero)
  refine ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hs⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).val, ?_⟩
  rw [map_units_inv, hu', hs]

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

theorem sabMap_cast_φ {S₁ S₂ : Scheme.{0}} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f f' : S₁ ⟶ S₂} (e : f = f')
    (m : SABMap t₁ t₂ f) : (e ▸ m : SABMap t₁ t₂ f').φ = m.φ := by
  subst e
  rfl

theorem exists_sabMap (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f) :
    ∃ m : SABMap 𝔐.t 𝔐₀.t h, 𝔐.m.φ = m.φ ≫ 𝔐₀.m.φ := by
  obtain ⟨m, e⟩ := sabCancel pullCubCancel E H _ _ _ Y.t 𝔐₀.t 𝔐.t 𝔐₀.f h 𝔐₀.m (hf ▸ 𝔐.m)
  exact ⟨m, by rw [← e, sabMap_cast_φ]⟩

theorem mem_abLocus_iff (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f)
    (x : 𝔐.X) : x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus 𝔐₀.t.G := by
  obtain ⟨m, -⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  have hp : IsPullback m.φ 𝔐.t.G.hom 𝔐₀.t.G.hom h := m.cart.1
  exact (abLocus_pullback abLocusOne 𝔐₀.t.semi hp x).symm

end Cover

section Maps

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem finrank_comp' {A B C : Type} [Field A] [Field B] [Field C] (f : A →+* B) (g : B →+* C) :
    (letI := (g.comp f).toAlgebra; Module.finrank A C) =
      (letI := f.toAlgebra; Module.finrank A B) * (letI := g.toAlgebra; Module.finrank B C) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank A B C).symm

theorem coordsAt_orbit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w w' : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (ho : SameOrbit w' w) : CoordsAt ξ y z w' := by
  obtain ⟨c, hc, rfl⟩ := ho
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := hw.1 k
    exact ⟨a, IsUnit.mk0 _ (mul_ne_zero (hc k) ha.ne_zero)⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := IsUnit.mk0 _ fun h0 => ha.ne_zero (by simp [h0])
    obtain ⟨h1, h2⟩ := hw.2 k a ha'
    refine ⟨h1, fun b => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 b
    exact ⟨r, hr, by simp only [e]; ring⟩

end Maps

section Orbit

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_sub_orbit {A B : HermLine J} (hab : A.a = B.a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) - Real.log (B.h w) = Real.log (A.h z) - Real.log (B.h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [log_h_smul A hc hz, log_h_smul B hc hz, hab]
  ring

theorem log_sum_orbit {X : Type} (s : Finset X) {A : HermLine J} {B : X → HermLine J}
    (hab : A.a = -∑ x ∈ s, (B x).a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ x ∈ s, Real.log ((B x).h w) = Real.log (A.h z) + ∑ x ∈ s, Real.log ((B x).h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  simp only [log_h_smul _ hc hz, Finset.sum_add_distrib]
  have : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ = -∑ x ∈ s, ∑ k, ((B x).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hab, ← Finset.sum_mul, ← neg_mul]
    simp [Finset.sum_apply]
  rw [this]
  ring

theorem pullDeg_neg_sum {K₀ : Type} {X : Type} {κ : K₀ → K} (hκ : Function.Injective κ) (s : Finset X) (f : X → K₀ → ℤ) :
    pullDeg κ (-∑ x ∈ s, f x) = -∑ x ∈ s, pullDeg κ (f x) := by
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    simp [pullDeg, hκ.extend_apply, Finset.sum_apply]
  · simp [pullDeg, Function.extend_apply' _ _ _ hk, Finset.sum_apply]

theorem log_tensor_pull {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {κ : K₀ → K}
    {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (A : HermLine J₀) (T : HermLine J) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((pullHerm hv A).tensor T).h z) = Real.log (A.h fun p => z (v p)) + Real.log (T.h z) :=
  Real.log_mul ((pullHerm hv A).pos z hz).ne' (T.pos z hz).ne'

end Orbit

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsValFam {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    {n : ℕ} (b : Fin n → Z.V) (v : Vecs y n) : Prop :=
  ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b i) v' ∧ SameVec Y y (v i) v'

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_cart_to_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)),
    ∃ φ₁ : tK.G.left ⟶ Y.t.G.left, IsGrpPullback tK.G Y.t.G (y ≫ Y.j) φ₁ ∧
      ∀ (u : epsAt (𝟙 (Sp K)) ⟶ tK.G) (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G),
        SameVec Y y v v' → u.left ≫ m.φ = v.left → u.left ≫ φ₁ = v'.left := by
  intro E _ _ _ H D l Xo c O _ β Y K _ y tK m
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hw : m.φ ≫ Xo.univ.t.G.hom = (tK.G.hom ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact m.cart.1.w
  let φ' : tK.G.left ⟶ Y.oF.t.G.left := hp.lift m.φ (tK.G.hom ≫ y) hw
  have h1 : φ' ≫ Y.m0.toSABMap.φ = m.φ := hp.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = tK.G.hom ≫ y := hp.lift_snd _ _ _
  have hn : IsGrpPullback tK.G Xo.univ.t.G (y ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) :=
    by rw [h1]; exact m.cart
  have hc : IsGrpPullback tK.G Y.oF.t.G y φ' := IsGrpPullback.cancel Y.m0.toSABMap.cart hn h2
  refine ⟨φ' ≫ Y.m.φ, IsGrpPullback.comp hc Y.m.cart, ?_⟩
  rintro u v v' ⟨u', a, b, e⟩ huv
  have hu : u.left ≫ φ' = u' := by
    apply hp.hom_ext
    · rw [Category.assoc, h1, huv, b]
    · have wu : u.left ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) ≫ 𝟙 (Sp K) := Over.w u
      rw [Category.assoc, h2, ← Category.assoc, wu, a, Category.comp_id]
  rw [← Category.assoc, hu, e]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end
