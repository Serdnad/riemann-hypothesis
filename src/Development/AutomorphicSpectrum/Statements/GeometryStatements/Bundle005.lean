module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat

def CptFlatInputs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c))
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (t : (c.F →+* ℂ) → ℝ) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (n : ℕ)
    (F' : Type) [Field F'] [NumberField F'] (ι : c.F →+* F') (ψ : F' →+* Ω),
    Z.IsGeom → FlatOnModel Z τ.1 φ → (∀ s, HasInfNorm U τ.1 φ s (t s)) →
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    ψ.comp ι = 𝔐.cst → (∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ) →
    Birational y → IsArithVar (mCoordIdeal y) n →
    Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) →
    IsSmoothHerm A → IsConjInvariantH A → A.a = ∑ i, xdeg (τ, i) →
    (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      A.h w = ∏ i, (hx (τ, i)).h w) →
    (∀ p ∈ S, ExactModLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (p : Ω) (D.p + D.q)) →
    (∀ p : ℕ, p.Prime → p ∉ S →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (p : Ω)) →
    ∃ (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), c₀ ≠ 0 ∧
      (∀ σ, cinf σ = Real.exp (t (σ.comp ι))) ∧
      (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p
          (c₀ * ∏ i, e (τ, i))) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
        ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ,
          (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) →
          OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))))
            (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) ∧
      (∀ σ, 0 < cinf σ) ∧
      ∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg →
        IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h →
          ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖

namespace CptInputs

theorem exists_constants {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} (hy : Birational y) {F : Type} [Field F] [NumberField F] (cst : F →+* Ω) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ι : F →+* F') (ψ : F' →+* Ω), ψ.comp ι = cst ∧
      ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ := by
  classical
  letI : Algebra F Ω := cst.toAlgebra
  have hle : ∀ g : MRing J, aeval y g ∈ IntermediateField.adjoin F (Set.range y) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]; exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  haveI : Algebra.EssFiniteType F Ω := by
    rw [← IntermediateField.fg_top_iff]
    refine ⟨(Set.finite_range y).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, eq_top_iff]
    intro a _
    obtain ⟨d, g, h, -, -, h0, e⟩ := hy a
    rw [eq_div_of_mul_eq h0 e.symm]
    exact div_mem (hle g) (hle h)
  let L := algebraicClosure F Ω
  haveI : FiniteDimensional F L := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType F Ω
  haveI : NumberField L := NumberField.of_module_finite F L
  refine ⟨L, inferInstance, inferInstance, algebraMap F L, algebraMap L Ω, rfl, ?_⟩
  rintro x ⟨f, hf, hx⟩
  have h1 : IsAlgebraic L x := ⟨f, hf, hx⟩
  exact ⟨⟨x, mem_algebraicClosure_iff.2 (h1.restrictScalars F)⟩, rfl⟩

end CptInputs

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl Filter Topology Metric

def FlatLineGeneratorComponent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → (∀ s : c.F →+* ℂ, ∃ t : ℝ, HasInfNorm U τ φ s t ∧ HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t) ∧ ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsFlatGen U τ φ FU i

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl Filter Topology Metric

def FlatLineGenerator : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → ∃ φ : FrameFn Xo c, IsLineFn U τ φ ∧ FlatOnModel Z τ φ ∧ ∀ φ' : FrameFn Xo c, IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal)

def HodgeLatticeFlagBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ [Fintype (CMType H)] [DecidableEq (CMType H)] (Fl : 𝔐.Flag) (S₀ : Finset ℕ)
      (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))), Fl.TwoLevels S₀ T →
    ∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ →
      ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => FlagChernComparison (pointIdeal O y) d p D.p φ (T.map (Int.castRingHom O))

end GlobalTheory.CompanionTheory.Ar
end

section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal)

def TrivFlagOnHodge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (Fl : 𝔐.Flag) (x : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω),
      Fl.RootLines x e → ∀ p ∈ S, HT.HTFree 𝔐 p →
      ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => ∀ τ W, IsFibreComp (pointIdeal O y) W →
        TrivFlagAt W fun i : Fin (D.p + D.q) => x (τ, i)

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open AlgebraicGeometry CategoryTheory NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def CmpPair : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ)
    (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'),
    Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) →
    IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) →
    ∀ w : Fin (Top.dimFl (CMType H) (D.p + D.q) + 1) → CMType H × Fin (D.p + D.q),
      Tendsto (fun t => II _ _ M.P _ (fun j => M.x t (w j)) / M.δ -
        II _ _ M'.P _ (fun j => M'.x t (π (w j).1, (w j).2)) / M'.δ) (𝓝[>] 0) (𝓝 0)

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end
