module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle025
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle031
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.PullDiv

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem exists_pullCart_agree : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hP U hU H
  classical
  have : CompactSpace Y₁ := compactSpace_of_isProjOver hP
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)

  have hinj : ∀ w₁ w₂ : Y₁, t w₁ ∈ U → t w₂ ∈ U → t w₁ = t w₂ → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ e
    have hb : Function.Injective (t ∣_ U) :=
      ((ConcreteCategory.bijective_of_isIso ((t ∣_ U).base))).1
    have := @hb ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ (Subtype.ext ((morphismRestrict_base_coe t U _).trans
      (e.trans (morphismRestrict_base_coe t U ⟨w₂, h₂⟩).symm)))
    exact congrArg Subtype.val this
  let c : Y₀ → ℤ := fun z => if h : ∃ w, t w = z ∧ z ∈ U then H.mult h.choose else 0
  have hc : ∀ w, t w ∈ U → c (t w) = H.mult w := by
    intro w hw
    have h : ∃ w', t w' = t w ∧ t w ∈ U := ⟨w, rfl, hw⟩
    simp only [c, dif_pos h]
    have e := h.choose_spec
    rw [hinj _ _ (by rw [e.1]; exact hw) hw e.1]
  have hsupp : Function.support c ⊆ t '' Function.support H.mult := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      exact ⟨w, by simpa [hc w hw] using hz, rfl⟩
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  have hfin : (Function.support c).Finite := (H.finite_support_mult.image _).subset hsupp
  have hcod : ∀ z, c z ≠ 0 → Order.coheight z = 1 := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      rw [hc w hw] at hz
      rw [← (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU w hw).1]
      exact CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_cartier_with_multiplicities Y₀ (fun x => AbelianProjective.ufd_stalk q x) c hfin hcod
  refine ⟨H₀, fun y hy hmem => ?_⟩
  have : GlobalTheory.IsNormalScheme Y₁ := (isNormalScheme_iff Y₁).mpr fun x =>
    ⟨inferInstance, have := AbelianProjective.ufd_stalk (t ≫ q) x
      UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  obtain ⟨z, hzy, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (H - pullCart t H₀)).2.1 y).1 hmem
  have hzU : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  apply hz
  have hm := CartierDiv.mult_add (H - pullCart t H₀) (pullCart t H₀) z
  rw [sub_add_cancel, (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU z hzU).2 H₀, hH₀, hc z hzU] at hm
  omega

end GlobalTheory.PullDiv
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy.CanonIso

theorem isNormalScheme_of_smooth' {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem ring_ne_top' {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : E.ring ≠ ⊤ := fun h =>
  IsDiscreteValuationRing.not_isField E.ring (by
    rw [h]
    exact MulEquiv.isField (Field.toIsField X.functionField) Subring.topEquiv.toMulEquiv)

theorem isAt_of_through' {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {z : X} {E F : DivOver p} (hF : F.IsAt z) (hE : E.Through z) : E.IsAt z := by
  have hle : F.ring ≤ E.ring := fun f hf => hE f ((hF f).1 hf)
  have := ValuationSubring.eq_of_le_of_ne_top F.ring hle (ring_ne_top' E)
  exact fun f => this ▸ hF f

theorem not_mem_supp_sub_pullCart : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)] (U : Y₀.Opens), (U : Set Y₀).Nonempty → IsIso (t ∣_ U) → ∀ (η : RatForms q n), η ≠ 0 → ∀ (K₀ : CartierDiv Y₀) (K₁ : CartierDiv Y₁), IsDivOfForm K₀ η → IsDivOfForm K₁ (EtaleKlt.ratPull q t n η) → ∀ y : Y₁, t y ∈ U → y ∉ (K₁ - pullCart t K₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ U hU hiso η hη K₀ K₁ h₀ h₁ y hy
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)
  haveI : GlobalTheory.IsNormalScheme Y₀ := isNormalScheme_of_smooth' q
  haveI : GlobalTheory.IsNormalScheme Y₁ := isNormalScheme_of_smooth' (t ≫ q)
  have hbir := GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' Y₀ Y₁ t U hU hiso
  have hpull : EtaleKlt.ratPull q t n η ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k Y₀ Y₁ q t hbir n).1 (h.trans (map_zero _).symm))
  rw [(GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (K₁ - pullCart t K₀)).2.1 y]
  rintro ⟨z, hzy, hz⟩
  apply hz
  have htz : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  obtain ⟨hc, hm⟩ := GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hiso z htz
  have hsub : (K₁ - pullCart t K₀).mult z = K₁.mult z - (pullCart t K₀).mult z := by
    have := CartierDiv.mult_add (K₁ - pullCart t K₀) (pullCart t K₀) z
    rw [sub_add_cancel] at this
    omega
  rw [hsub, hm K₀, sub_eq_zero]
  by_cases h1 : Order.coheight z = 1
  · obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := t ≫ q) h1
    obtain ⟨E, hO⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k Y₀ Y₁ q t hbir E'
    obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) (z := t z) (hc ▸ h1)
    have hthr : E.Through (t z) := by
      intro f hf
      obtain ⟨a, rfl⟩ := hf
      exact (hO _).2 ((hE' _).2 ⟨t.stalkMap z a, (GlobalTheory.functionFieldMap_algebraMap t z a).symm⟩)
    have hE : E.IsAt (t z) := isAt_of_through' hF hthr
    rw [← GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y₁ (t ≫ q) n _ hpull K₁ h₁ E' z hE',
      ← GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y₀ q n η hη K₀ h₀ E (t z) hE]
    exact GlobalTheory.T.form_order_birational_pullback k Y₀ Y₁ q t hbir E' E hO n η hη
  · have a : K₁.mult z = 0 := by_contra fun h => h1 (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    have b : K₀.mult (t z) = 0 :=
      by_contra fun h => h1 (hc ▸ CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    rw [a, b]

end GlobalTheory.Discrepancy.CanonIso
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.isAt_lift : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E →
    ∀ z : X, E.IsAt z → ∃ w : Y, s w = z ∧ E'.IsAt w := by
  intro k _ X Y _ _ p s _ hbij hprop E' E hOver z hz
  obtain ⟨w, hw, hwt⟩ := GlobalTheory.T.divisor_center_proper_lift k X Y p s hbij hprop E' E hOver z
    (hz.through specializes_rfl)
  subst hw
  refine ⟨w, rfl, fun f => ⟨fun hf => ?_, hwt f⟩⟩
  obtain ⟨g, rfl⟩ := hbij.2 f
  obtain ⟨a, rfl⟩ := (hz g).1 ((hOver g).2 hf)
  exact ⟨s.stalkMap w a, (GlobalTheory.functionFieldMap_algebraMap s w a).symm⟩

end GlobalTheory.Discrepancy
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.klt_of_snc_coefficients : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  first | exact @_root_.GlobalTheory.Discrepancy.coeff_criterion_snc | exact _root_.GlobalTheory.Discrepancy.coeff_criterion_snc | (intros; apply _root_.GlobalTheory.Discrepancy.coeff_criterion_snc <;> assumption)
end
