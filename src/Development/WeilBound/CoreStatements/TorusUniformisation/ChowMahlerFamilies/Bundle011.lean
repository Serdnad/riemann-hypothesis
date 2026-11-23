module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle040
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem PositivityTheory.Xgn.t_bundle_of_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
  classical
  intro O _ Ω _ _ K _ _ ι _ x N V _ _
  refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
  refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
            stable := ?_
            frame := ?_
            overlap := ?_ }, ?_⟩
  · intro s a ha e he
    by_cases h : mseg x s = 0
    · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
      rw [he, smul_zero]
    · simp only [h, if_false] at he ⊢
      exact hfam.1 s h a ha e he
  · intro s hs
    simp only [hs, if_false]
    exact (hloc s hs).2
  · intro s t hs ht e he
    simp only [hs, ht, if_false] at he ⊢
    exact hfam.2 s t hs ht e he
  · intro s hs
    simp only [hs, if_false]
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.line_lattice_generator_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → t ≠ 0 → (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → L.IsGenAt q t) → L.IsGenAt p t := by
  intro X Ω _ ξ _ hg hn L T p t hL hT ht hq
  obtain ⟨U, hU, b, -, h⟩ := hL p (hT p specializes_rfl)
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  have hgen : ∀ q : Cpt ξ, q.1 ⤳ p.1 → b 0 ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {b 0} := by
    intro q hqp
    obtain ⟨h1, h2⟩ := h q (hT q hqp) (hqp.mem_open U.2 hU)
    exact ⟨h1.ne_zero 0, by rw [h2, hr]⟩
  obtain ⟨he, hp⟩ := hgen p specializes_rfl
  have hu : ∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → unitAt ξ q (t / b 0) := by
    intro q hqp hd
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht ((hq q hqp hd).2.symm.trans (hgen q hqp).2)
    rwa [e, smul_eq_mul, mul_div_cancel_right₀ _ he]
  have h1 : t / b 0 ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.1
  have h2 : (t / b 0)⁻¹ ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.2
  refine ⟨ht, ?_⟩
  rw [hp]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · refine ⟨⟨_, h2⟩, ?_⟩
    change (t / b 0)⁻¹ * t = b 0
    field_simp
  · refine ⟨⟨_, h1⟩, ?_⟩
    change (t / b 0) * b 0 = t
    field_simp
end
