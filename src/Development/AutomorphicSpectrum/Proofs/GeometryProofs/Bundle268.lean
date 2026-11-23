module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle264
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle266
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.gram_matrix_change_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ' → Γ = Γ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_model_prime_degree : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (t : CMType H ⊕ CMType H), ∃ i : (Fin (labelRk D t) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p t) (b t) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p t.swap) (b t.swap) c')) i (qMap P (b t.swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb t a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p t) (b t) c') (b t) i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq.seq_holds | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq.seq_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq.seq_holds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.ConstEmbedding

theorem exists_spMap {A : Type} [CommRing A] (x : Sp ℂ ⟶ Sp A) : ∃ ψ : A →+* ℂ, spMap ψ = x :=
  ⟨(Spec.preimage x).hom, by
    show Spec.map (CommRingCat.ofHom (Spec.preimage x).hom) = x
    simp⟩

theorem exists_extend (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* ℂ) :
    ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = ψ := by
  have hinj : Function.Injective ψ :=
    GlobalTheory.CompanionTheory.Ar.GrNorm.injective_of_algebraic (algebraMap (𝓞 F) F)
      (IsFractionRing.injective (𝓞 F) F) ψ
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun a => ?_⟩
  simp

theorem exists_embedding (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)) (hol : IsHolTo (Metric.ball 0 1) p) :
    ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  choose ψ hψ using fun u => exists_spMap (p u ≫ q)
  choose κ hκ using fun u => exists_extend F (ψ u)
  have hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) (Metric.ball 0 1) := by
    intro a
    have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hol q
    have h3 := (h2 ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv a)).2
    have hset : Metric.ball (0 : Fin n → ℂ) 1 ⊆ {b ∈ Metric.ball (0 : Fin n → ℂ) 1 | ⊤ ≤ (p b ≫ q) ⁻¹ᵁ ⊤} :=
      fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (a : F) = valAt' (p b ≫ q) ⊤ _
    rw [← hψ b, ← hκ b]
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 F) F)) a).symm
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  refine ⟨κ 0, fun u hu => ?_⟩
  have hc := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected (convex_ball (0 : Fin n → ℂ) 1).isPreconnected κ hd hu h0
  rw [← hc, hκ u, hψ u]

end GlobalTheory.CompanionTheory.Ar.ConstEmbedding
end
