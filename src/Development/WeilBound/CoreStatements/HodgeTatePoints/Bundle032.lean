module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle023
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle019
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle020
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle014
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle015
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GdChart
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle029
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle030
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem chart_le_regAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (s : ∀ k, J k) (q : Cpt 𝔐.ξ) (hs : InChart 𝔐.ξ (mseg y) s q) (hq : OverZp 𝔐 p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  have ha : (a : Ω) ∈ Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) :=
    (Hcptgen.chartRing_mseg (o := o) y s hs.1).le a.2
  obtain ⟨b, hb, h⟩ := Hcptgen.mem_adjoin_loc Fact.out ho _ ha
  have h3 := (𝔐.tie.ring s hs.1 _).1 h q hs
  have h4 := (Hcptgen.overZp_iff Fact.out q).1 hq b hb
  have := mul_mem h3 h4.2.2
  rwa [mul_assoc, mul_inv_cancel₀ h4.1, mul_one] at this

end PositivityTheory.HtPt.Htat
end
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Ge

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  classical
  haveI := Module.finitePresentation_of_projective A M
  let S := nonZeroDivisors A
  let F := Localization S
  let f := LocalizedModule.mkLinearMap S M
  let g := Algebra.linearMap A F
  have e1 : finrank A (Module.Dual A M) = finrank A (LocalizedModule S M →ₗ[F] F) :=
    (IsLocalizedModule.finrank_eq S (IsLocalizedModule.mapExtendScalars S f g F) le_rfl).symm
  rw [e1, ← IsLocalization.finrank_eq F S le_rfl, Subspace.dual_finrank_eq,
    IsLocalization.finrank_eq F S le_rfl, IsLocalizedModule.finrank_eq S f le_rfl]

theorem ringOfIntegers_mem_range (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {E : Type} [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

def qLin {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem chart_sequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hκ htest hproj'
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right κ _) hκ
  have h1 := PositivityTheory.HtPt.Gc.chart_ii A K E c hc p R N Ω D κ hκR hproj' htest
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hint : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hr⟩ :=
    PositivityTheory.HtPt.Ga.dual_map A K hinj E c hc p R N Ω D κ σ d m hint hd hκ h1.2 hP2
  obtain ⟨-, -, hsurj⟩ := PositivityTheory.HtPt.Ga.q_surj A K hinj E c hc p R N Ω D κ σ m (hint σ) hκ h1.2
  have hcz := PositivityTheory.HtPt.Gd.chart_comp_zero A K E c hc p R N Ω D κ σ d d' m i hκ hd hd' h1.2
    hP1 hP2 htest hi
  refine ⟨i, hi, hr i hi, ?_, hsurj⟩
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu⟩ := hu
      refine ⟨0, (↑u⁻¹ : A) ^ m • x, ?_⟩
      rw [map_zero, zero_add, smul_smul, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D σ)
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) :=
        Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D _)
      let q' : (Fin N → A) →ₗ[A] D.omHT σ :=
        (qLin D σ).codRestrict (D.omHT σ) (PositivityTheory.HtPt.Ga.q_mem D σ)
      have hrank : finrank A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) +
          finrank A (D.omHT σ) = N := by
        rw [finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom)), add_comm]
        exact PositivityTheory.HtPt.Gb.chart_rank A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 htest
      obtain ⟨rr, hrr⟩ := hr i hi
      obtain ⟨w, x', hx⟩ := PositivityTheory.HtPt.Gd.split_exact A
        (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m) i rr q' hrank hrr
        (fun z => by
          obtain ⟨x0, y', hy', h⟩ := hsurj z.1 z.2
          exact ⟨x0, ⟨y', hy'⟩, Subtype.ext h⟩)
        (fun w => by
          obtain ⟨y0, hy0, h0⟩ := hcz w
          exact ⟨⟨y0, hy0⟩, Subtype.ext h0⟩)
        x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      exact ⟨w, x', hx⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y0, hy0, h0⟩ := hcz w
    refine ⟨y0 + D.q σ x', (D.omHT σ).add_mem hy0 (PositivityTheory.HtPt.Ga.q_mem D σ x'), ?_⟩
    have hq : ∀ z, D.q σ z = qLin D σ z := fun _ => rfl
    rw [hq, map_add (f := _), map_smul, ← hq, ← hq, h0, smul_add]
    all_goals rfl

end PositivityTheory.HtPt.Ge
end
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem curve_sec_nef : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (W : Ideal (MRing J)) (a : K → ℤ) (r : (∀ k, J k) → Ω), IsMultiProjPrime W → mCoordIdeal y ≤ W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → (∀ s, mseg y s ≠ 0 → r s ∈ chartRing o (mseg y) s) → (∀ s t, mseg y s ≠ 0 → mseg y t ≠ 0 → ∃ (n : ℕ) (z : Ω), z ∈ chartRing o (mseg y) t ∧ (mseg y s / mseg y t) ^ n * (r s * chartMon y s a / chartMon y t a - r t) = p * z) → (∃ (s : ∀ k, J k) (n d : ℕ) (g : MRing J), (∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) ∧ ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∉ W ∧ n * r s * mseg y s ^ d = aeval y g) → 0 ≤ geoNum 1 W (fun _ => a) := by
  intro Ω _ _ K _ J _ y p _ o _ _ ho W a r hW hle hch hdim hr hov ⟨s, n, d, g, hs, hn, hg, hgW, hgy⟩
  have hp := natCast_mem_of_charOf hch
  have hP := hW.1
  have hs0 := mseg_ne_zero hle hs
  let ap : K → ℕ := fun k => (a k).toNat
  let am : K → ℕ := fun k => (-a k).toNat
  refine geoNum_nonneg_of_regular p hW hp hdim (hom_mul hg (hom_mon s ap))
    (hom_mul (hom_mon s fun _ => d) (hom_mon s am)) (fun k => ?_)
    (fun h => (hP.mem_or_mem h).elim hgW (mon_not_mem hP hs _))
    (fun h => (hP.mem_or_mem h).elim (mon_not_mem hP hs _) (mon_not_mem hP hs _)) fun t ht => ?_
  · simp only [Pi.add_apply, ap, am]
    omega
  have ht0 := mseg_ne_zero hle ht
  obtain ⟨m, z, hz, hrel⟩ := hov s t hs0 ht0
  obtain ⟨n₁, e₁, g₁, hn₁, hg₁, hy₁⟩ := exists_rep ho ht0 (hr t ht0)
  obtain ⟨n₂, e₂, g₂, hn₂, hg₂, hy₂⟩ := exists_rep ho ht0 hz
  refine ⟨n₁ * n₂, (fun _ => e₁ + e₂) + am, n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap)),
    fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hn₁ hn₂, ?_⟩
  have hsplit : mon t ((fun _ => e₁ + e₂) + am) = mon t (fun _ => e₁ + e₂) * mon t am := by
    simp [mon, pow_add, Finset.prod_mul_distrib]
  have hz0 : mon s (fun _ => m) * (((n₁ * n₂ : ℕ) : MRing J) * (mon t (fun _ => e₁ + e₂) * mon t am * (g * mon s ap)) -
      n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap * (mon s (fun _ => d) * mon s am)))) -
      p * (n * (n₁ * (g₂ * mon t (fun _ => e₁ + m) * mon s (fun _ => d) * mon s am * mon t ap))) ∈
        mCoordIdeal y := by
    refine mem_mCoordIdeal (d := fun k => m + e₁ + e₂ + d + ap k + am k) (hom_sub (hom_of_eq (hom_mul (hom_mon _ _)
      (hom_sub (hom_nat_mul _ (hom_mul (hom_mul (hom_mon _ _) (hom_mon _ _)) (hom_mul hg (hom_mon _ _))))
        (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul hg₁ (hom_mon _ _)) (hom_mon _ _))
          (hom_mul (hom_mon _ _) (hom_mon _ _))) fun k => ?_))))) fun k => ?_)
      (hom_nat_mul _ (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul (hom_mul hg₂ (hom_mon _ _))
        (hom_mon _ _)) (hom_mon _ _)) (hom_mon _ _)) fun k => ?_))))) ?_
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    rw [chartMon_eq_div hs0, chartMon_eq_div ht0] at hrel
    have hne : ∀ {u : ∀ k, J k}, mseg y u ≠ 0 → ∀ c, aeval y (mon u c) ≠ 0 := fun hu c => by
      rw [aeval_mon]
      exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Finset.prod_ne_zero_iff.1 hu k (Finset.mem_univ k))
    have h1 := hne hs0 am
    have h2 := hne ht0 am
    have h3 := hne ht0 ap
    simp only [map_sub, map_mul, map_natCast, aeval_mon_const, ← hgy, ← hy₁, ← hy₂]
    change (mseg y s / mseg y t) ^ m * (r s * (aeval y (mon s ap) / aeval y (mon s am)) /
      (aeval y (mon t ap) / aeval y (mon t am)) - r t) = p * z at hrel
    generalize aeval y (mon s ap) = A at *
    generalize aeval y (mon s am) = B at *
    generalize aeval y (mon t ap) = A' at *
    generalize aeval y (mon t am) = B' at *
    rw [div_pow] at hrel
    field_simp at hrel
    push_cast
    linear_combination (n * n₁ * n₂ * mseg y t ^ (e₁ + e₂) * mseg y s ^ d) * hrel
  have h1 := (Ideal.add_mem_iff_left W (W.neg_mem (W.mul_mem_right _ hp))).1 (by
    rw [← sub_eq_add_neg]; exact hle hz0)
  have h2 := (hP.mem_or_mem h1).resolve_left (mon_not_mem hP hs _)
  rw [hsplit]
  convert h2 using 1
  ring

end PositivityTheory.HtPt.Gf
end
