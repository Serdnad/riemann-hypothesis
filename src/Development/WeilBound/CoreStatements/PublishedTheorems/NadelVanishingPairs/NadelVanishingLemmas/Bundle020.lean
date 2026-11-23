module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle019
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle012
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle018
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_generic_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_spread | exact _root_.GlobalTheory.LogPair.relSnc_spread | (intros; apply _root_.GlobalTheory.LogPair.relSnc_spread <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.log_forms_lattice_finite : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ) (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  first | exact @_root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC | exact _root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC | (intros; apply _root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC <;> assumption)
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_eq_extD_imp_eq_zero :
    ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ)
      (γ : abelian₂ K →+* abelian₂ K), IsCoord x → IsCartierMap p x γ → ∀ ζ ξ : abelian₂ K, γ ζ = extD K ξ → ζ = 0 := by
  intro K _ p _ _ n x γ hx hγ ζ ξ hζ
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hx
  have hmem : ζ ∈ Submodule.span K (Set.range (logWedge x)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  obtain ⟨-, Q, π, -, hQ, -, hπ, hQd, -⟩ := GlobalTheory.T.cartier_projection_properties K p n x hx
  have hγs : γ (∑ I, c I • logWedge x I) = ∑ I, (c I ^ p) • logWedge x I := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ (c I) I
  have hfix : Q (γ (∑ I, c I • logWedge x I)) = γ (∑ I, c I • logWedge x I) := by

    rw [hγs, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQ, hπ]
  have h0 : ∑ I, (c I ^ p) • logWedge x I = 0 := by
    rw [← hγs, ← hfix, hζ, hQd]
  have hc : ∀ I, c I ^ p = 0 := fun I =>
    (Fintype.linearIndependent_iff.1 hli) (fun I => c I ^ p) h0 I
  have hc' : ∀ I, c I = 0 := fun I =>
    (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 (hc I)
  simp [hc']

end GlobalTheory
end

section

set_option autoImplicit false

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem logCartier_rounding_family : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)
    (x : Fin n → Kˣ) (J : Finset (Fin n)) (γ : abelian₂ K →+* abelian₂ K) (Y : Type) [Nonempty Y] (A : Y → Subring K)
    (t : Y → Kˣ) (r : Y → Fin n → ℕ), (∀ y, _root_.GlobalTheory.LogDR.AlgChart (A y) x) → (∀ y j, r y j < p) → IsCartierMap p x γ →
    ∀ (a : ℕ) (η : abelian₂ K), (∀ y, η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) a) →
    extD K η = 0 → ∃ ζ ξ : abelian₂ K, (∀ y, ζ ∈ chartForms (A y) x J (t y) a) ∧
      (∀ y q, q + 1 = a → ξ ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (a = 0 → ξ = 0) ∧ η = γ ζ + extD K ξ := by
  intro K _ p _ _ n x J γ Y _ A t r hA hr hγ a η hη hd
  obtain ⟨y0⟩ := ‹Nonempty Y›
  have hc : IsCoord x := (hA y0).coord
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h, Q, π, hhom, hQw, hπ, -, -, hstab⟩ := GlobalTheory.T.cartier_projection_properties K p n x hc
  have hT : ∀ y, (∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) (q + 1),
        h η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) 0, h η = 0) ∧
      ∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q,
        Q η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q := by
    intro y
    exact hstab (fun q => chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q)
      (GlobalTheory.T.chart_forms_differential_closed K p (A y) n x J (t y) (r y) (hA y))
      (fun i θ hθ => GlobalTheory.T.euler_contraction_chart_forms K (A y) n x J _ i θ (hA y).mem hθ)
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hc
  obtain ⟨c, hcη⟩ : ∃ c : Finset (Fin n) → K, ∑ I, c I • logWedge x I = η :=
    (Submodule.mem_span_range_iff_exists_fun K).mp (hsp ▸ Submodule.mem_top)
  choose g hg using fun I => hπ (c I)
  have hQη : Q η = ∑ I, g I ^ p • logWedge x I := by

    rw [← hcη, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQw, hg]
  refine ⟨∑ I, g I • logWedge x I, h η, ?_, ?_, ?_, ?_⟩
  · intro y
    have hm := (hT y).2.2 a η (hη y)
    rw [GlobalTheory.T.mem_chart_forms_iff] at hm
    obtain ⟨c', hc'0, hc'A, hc'eq⟩ := hm
    have heq : ∀ I, c' I = g I ^ p := by
      have h0 : ∑ I, (c' I - g I ^ p) • logWedge x I = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hc'eq, ← hQη, sub_self]
      intro I
      exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 I)
    rw [GlobalTheory.T.mem_chart_forms_iff]
    refine ⟨g, ?_, ?_, rfl⟩
    · intro I hI
      have h1 := hc'0 I hI
      rw [heq] at h1
      exact (pow_eq_zero_iff hp.ne').mp h1
    · intro I
      have h1 := hc'A I
      rw [heq] at h1
      exact GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem K p (A y) n x I J (t y) (r y) (g I) hp (hA y) (hr y) h1
  · intro y q hq
    subst hq
    exact (hT y).1 q η (hη y)
  · intro ha
    subst ha
    exact (hT y0).2.1 η (hη y0)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ]
    rw [← hQη]
    have h2 := hhom η
    rw [hd, map_zero, add_zero] at h2
    exact sub_eq_iff_eq_add'.mp h2

end GlobalTheory
end
