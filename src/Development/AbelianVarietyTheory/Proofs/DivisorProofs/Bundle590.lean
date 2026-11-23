module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PrismaticFilteredAtOfIntegersAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem existsUnique_padic_of_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O,
      WittVector.frobenius a = WittVector.frobenius (xi ε) * a →
        ∃! c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p := by
    simpa [zeta] using hε 1
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsDomain (Ainf p O) := GlobalTheory.Sandwich.Model.isDomain_Ainf hv
  have hμ : Sandwich.mu ε ≠ 0 := GlobalTheory.Sandwich.Model.mu_ne_zero (hε := h1) hv
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.Prism.exists_padic_of_eigen h1 ha
  have hinj : Function.Injective (ofPadic p O) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact ⟨c, hc, fun c' hc' => hinj (mul_right_cancel₀ hμ (hc'.trans hc.symm))⟩

end GlobalTheory.PDivLat
end
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_ainfSandwichDatum_blockSum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (h₁ h₂ : ℕ) (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]), ∃ D : Datum ε (h₁ + h₂) ℤ_[p], (∀ x y, D.al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y)) ∧ ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  first | exact @GlobalTheory.BlockSum.exists_sum_datum | exact GlobalTheory.BlockSum.exists_sum_datum | (intros; apply GlobalTheory.BlockSum.exists_sum_datum <;> assumption)
end

section

open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.LaplaceStrip

theorem norm_integrand {α : Type} (ℓ : α → ℝ) (g : α → ℂ) (s : ℂ) (x : α) :
    ‖g x * Complex.exp (s * (ℓ x : ℂ))‖ = ‖g x‖ * Real.exp (s.re * ℓ x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem laplace_entire_boundedInStrips {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    hg.mul (by fun_prop : Measurable fun x => Complex.exp (s * (ℓ x : ℂ))).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    (hint s.re).mono' (hmeas s) (Filter.Eventually.of_forall fun x => (norm_integrand ℓ g s x).le)
  refine ⟨fun s₀ => ?_, fun a b _ => ⟨∫ x, ‖g x‖ * Real.exp (b * ℓ x) ∂μ, fun s _ hsb => ?_⟩⟩
  · have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => g x * Complex.exp (s * (ℓ x : ℂ)))
      (F' := fun s x => g x * (Complex.exp (s * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))))
      (x₀ := s₀) (bound := fun x => ‖g x‖ * Real.exp ((s₀.re + 2) * ℓ x)) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall hmeas) (hI s₀)
      (hg.mul (by fun_prop : Measurable fun x =>
        Complex.exp (s₀ * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))).aestronglyMeasurable)
      ?_ (hint _) ?_
    · exact key.2.differentiableAt
    · filter_upwards [hpos] with x hx s hs
      have hre : s.re ≤ s₀.re + 1 := by
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := (abs_le.mp h1).2
        simp only [Complex.sub_re] at h3
        linarith
      rw [one_mul, ← mul_assoc, norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have e1 : Real.exp (s.re * ℓ x) ≤ Real.exp ((s₀.re + 1) * ℓ x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hx)
      have e2 : ℓ x ≤ Real.exp (ℓ x) := by linarith [Real.add_one_le_exp (ℓ x)]
      have e3 : Real.exp ((s₀.re + 2) * ℓ x) = Real.exp ((s₀.re + 1) * ℓ x) * Real.exp (ℓ x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e3, mul_assoc]
      gcongr
    · exact Filter.Eventually.of_forall fun x s _ => by
        have := (((hasDerivAt_id s).mul_const (ℓ x : ℂ)).cexp).const_mul (g x)
        simpa using this
  · refine norm_integral_le_of_norm_le (hint b) ?_
    filter_upwards [hpos] with x hx
    rw [norm_integrand]
    gcongr

end GlobalTheory.LaplaceStrip
end
end

section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.DiscClass

theorem G_eq_of_mul (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) (k : ℕ) :
    Λ.G k = u ^ k * Λ'.G k := by
  let e : (Λ.lattice : Set ℂ) ≃ (Λ'.lattice : Set ℂ) :=
    (Equiv.mulLeft₀ u hu).subtypeEquiv fun w => by simpa using (h w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : (Λ'.lattice : Set ℂ)) : ℂ) = u * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), one_mul]

theorem latDisc_eq_of_mul (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) :
    latDisc Λ = u ^ 12 * latDisc Λ' := by
  simp only [latDisc, PeriodPair.g₂, PeriodPair.g₃, G_eq_of_mul Λ Λ' u hu h 4, G_eq_of_mul Λ Λ' u hu h 6]
  ring

theorem abs_norm_eq_norm_sq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (x : K) :
    ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ‖φK x‖ ^ 2 := by
  have hcx : (InfinitePlace.mk φK).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro e
    apply hc
    ext y
    simp only [RingHom.comp_apply]
    rw [← ComplexEmbedding.conjugate_coe_eq, e]
  have hpos : 0 < InfinitePlace.nrComplexPlaces K := by
    classical
    unfold InfinitePlace.nrComplexPlaces
    convert Fintype.card_pos_iff.2 (⟨⟨_, hcx⟩⟩ : Nonempty {w : InfinitePlace K // w.IsComplex})
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
  have huniq : ∀ w : InfinitePlace K, w = InfinitePlace.mk φK := fun w =>
    Fintype.card_le_one_iff.1 hcard.le w _
  have hp := InfinitePlace.prod_eq_abs_norm x
  have e : (∏ w : InfinitePlace K, w x ^ w.mult) = InfinitePlace.mk φK x ^ (InfinitePlace.mk φK).mult := by
    rw [Fintype.prod_eq_single (InfinitePlace.mk φK) fun w hw => absurd (huniq w) hw]
  rw [← hp, e, InfinitePlace.apply, InfinitePlace.mult_isComplex ⟨_, hcx⟩]

theorem nrm_pow_mul_norm_latDisc_eq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair)
    (ha : IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa) (hb : IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb)
    (hcl : ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by

  have h1 : ClassGroup.mk K (𝔟 * 𝔞⁻¹) = 1 := by rw [map_mul, map_inv, ← hcl, mul_inv_cancel]
  obtain ⟨c, hcE⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hb' : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ c * 𝔞 := by
    rw [← hcE, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply 𝔟.ne_zero
    rw [hb', FractionalIdeal.spanSingleton_zero, zero_mul]
  have hu : φK c ≠ 0 := (map_ne_zero φK).2 hc0

  have hlat : ∀ w, φK c * w ∈ Λb.lattice ↔ w ∈ Λa.lattice := by
    intro w
    have eb : φK c * w ∈ Λb.lattice ↔ φK c * w ∈ φK '' ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← hb]; rfl
    have ea : w ∈ Λa.lattice ↔ w ∈ φK '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← ha]; rfl
    rw [eb, ea]
    constructor
    · rintro ⟨y, hy, e⟩
      have hy' : y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) := hy
      rw [hb', FractionalIdeal.mem_singleton_mul] at hy'
      obtain ⟨y', hy', rfl⟩ := hy'
      refine ⟨y', hy', ?_⟩
      rw [map_mul] at e
      exact mul_left_cancel₀ hu e
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c * y, ?_, map_mul _ _ _⟩
      show c * y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)
      rw [hb', FractionalIdeal.mem_singleton_mul]
      exact ⟨y, hy, rfl⟩
  have hD := latDisc_eq_of_mul Λa Λb (φK c) hu hlat

  have hN : nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = ‖φK c‖ ^ 2 * nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    unfold nrm
    rw [hb', map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, abs_norm_eq_norm_sq φK h2 hc c]
  rw [hN, hD, norm_mul, norm_pow]
  ring

end GlobalTheory.DiscClass
end
end

section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped IntermediateField

namespace GlobalTheory.QuadInHost

theorem exists_quadField : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  intro E _ _ I _ d φ hF hd4 Λ hΛ
  obtain ⟨hp, hd, -, -, -, hI, -, w, hw, hφw⟩ := hF
  have hd0 : (0 : ℚ) < d := by exact_mod_cast hp.pos
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval w (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ) = 0 := by
    simp [hw]
  have hi : IsIntegral ℚ w := ⟨_, hm, he⟩
  have h2 : Module.finrank ℚ ℚ⟮w⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hi]
    refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ w hm he)).trans
      (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
    rintro ⟨q, hq⟩
    have h1 : (algebraMap ℚ E q) ^ 2 = -(d : E) := by rw [hq]; exact hw
    have h3 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ E).injective (by simpa using h1)
    nlinarith [sq_nonneg q]
  let r : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hr : r ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [r] using hw)
  let φK : ℚ⟮w⟯ →+* ℂ := (φ i₀).comp (algebraMap ℚ⟮w⟯ E)
  have hφr : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) r = Complex.I * (Real.sqrt d : ℂ) := fun i => hφw i
  have hsq : (Real.sqrt d : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hp.pos)
    exact_mod_cast this.ne'
  refine ⟨ℚ⟮w⟯, h2, GlobalTheory.discr_eq_neg_of_sq_eq h2 hp.squarefree hd4 hr, φK, ?_, ?_, ?_⟩
  · intro i
    have := (IntermediateField.adjoin.powerBasis hi).algHom_ext
      (f := ((φ i).comp (algebraMap ℚ⟮w⟯ E)).toRatAlgHom) (g := φK.toRatAlgHom)
      (by simp only [IntermediateField.adjoin.powerBasis_gen]; exact (hφr i).trans (hφr i₀).symm)
    exact congrArg AlgHom.toRingHom this
  · intro h
    have := congrArg (fun f => f r) h
    simp only [RingHom.comp_apply] at this
    change starRingEnd ℂ (φK r) = φK r at this
    rw [show φK r = _ from hφr i₀] at this
    simp [Complex.conj_ofReal] at this
    have h0 : (2 * Complex.I) * (Real.sqrt d : ℂ) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h0 with h0 | h0
    · simp at h0
    · exact hsq h0
  · obtain ⟨ω, hω2, hgen⟩ := GlobalTheory.exists_integer_generator_of_sq_eq_neg h2 hp.squarefree hd4 hr
    have hφω : φK ω = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
      have := congrArg φK hω2
      rw [map_mul, map_add (f := _), map_one, map_ofNat, show φK r = _ from hφr i₀] at this
      linear_combination this / 2
    unfold IsLatOf
    ext x
    rw [SetLike.mem_coe, hΛ x]
    constructor
    · rintro ⟨hx, a, b, rfl⟩
      let y : ℚ⟮w⟯ := a + b * r
      have hy : φK y = a + b * (Complex.I * (Real.sqrt d : ℂ)) := by
        simp only [y, map_add (f := _), map_mul, map_ratCast, show φK r = _ from hφr i₀]
      have hint : IsIntegral ℤ y := by
        rw [← hy] at hx
        exact (isIntegral_algHom_iff φK.toIntAlgHom φK.injective).1 hx
      refine ⟨y, ?_, hy⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨⟨y, hint⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff] at hy
      obtain ⟨c, rfl⟩ := hy
      refine ⟨(RingOfIntegers.isIntegral_coe c).map φK.toIntAlgHom, ?_⟩
      obtain ⟨m, n, rfl⟩ := hgen c
      refine ⟨m + n / 2, n / 2, ?_⟩
      change φK ((m + n * ω : 𝓞 ℚ⟮w⟯) : ℚ⟮w⟯) = _
      push_cast
      simp only [map_add (f := _), map_mul, hφω]
      simp
      ring

end GlobalTheory.QuadInHost
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.FlatDescent

theorem injective_app_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : Function.Injective (p.app U) := by
  have := effectiveEpi_morphismRestrict p U
  intro a b hab
  have hb : Function.Bijective U.topIso.inv := ConcreteCategory.bijective_of_isIso _
  apply hb.1
  apply injective_appTop_of_epi (p ∣_ U)
  rw [appTop_morphismRestrict_apply, appTop_morphismRestrict_apply, hab]

theorem unit_ext_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {U : X.Opens} {a b : Γ(X, U)ˣ} (h : ∀ y : Y, p y ∈ U → gm p y U a = gm p y U b) : a = b := by
  have e : pullU p U a = pullU p U b := unit_ext fun y hy => by
    rw [gm_pull (𝟙 Y) p y U hy, gm_pull (𝟙 Y) p y U hy, Category.id_comp]
    exact h y hy
  exact Units.ext (injective_app_of_flat p U (congrArg Units.val e))

theorem exists_unit_of_gm_eq {X X' Z : Scheme.{0}} (f : X' ⟶ X) [Flat f] [Surjective f] [QuasiCompact f]
    {g₁ g₂ : Z ⟶ X'} (h : IsPullback g₁ g₂ f f) (U : X.Opens) (s : Γ(X', f ⁻¹ᵁ U)ˣ)
    (hs : ∀ z : Z, f (g₁ z) ∈ U → gm g₁ z _ s = gm g₂ z _ s) :
    ∃ a : Γ(X, U)ˣ, pullU f U a = s := by
  have hg : g₁ ⁻¹ᵁ f ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w]
  have e : res le_rfl (pullU g₁ _ s) = res hg (pullU g₂ _ s) := unit_ext fun z hz => by
    rw [gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 Z) g₁ z _ hz, gm_pull (𝟙 Z) g₂ z _ (hg hz),
      Category.id_comp, Category.id_comp]
    exact hs z hz
  obtain ⟨a, ha, -⟩ := (existsUnique_app_eq_iff f h U _ rfl le_rfl hg s.val).2 (congrArg Units.val e)
  obtain ⟨a, rfl⟩ := (isUnit_app_iff f U a).1 (ha ▸ s.isUnit)
  exact ⟨a, Units.ext ha⟩

theorem triv_of_gen_descent : ∀ {X X' Z : Scheme.{0}} (M : LB X), M.IsLB → ∀ (f : X' ⟶ X), Flat f →
    Surjective f → QuasiCompact f → ∀ (g₁ g₂ : Z ⟶ X'), IsPullback g₁ g₂ f f →
    ∀ t : LB.Gen (M.pull f), t.IsGen →
    (∀ (z : Z) (J : (Z ⟶ X) → M.ι), Geo.Tor.Good M z J → val t g₁ z J = val t g₂ z J) → Triv M := by
  intro X X' Z M hM f _ _ _ g₁ g₂ h t ht hv
  have le : ∀ i, f ⁻¹ᵁ M.U i ≤ LB.wchart M (fun _ : PUnit => f) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  have ex : ∀ i, ∃ a : Γ(X, M.U i)ˣ, pullU f _ a = res (le i) (t.s fun _ => i) := fun i =>
    exists_unit_of_gm_eq f h (M.U i) _ fun z hz => by
      have hz₂ : f (g₂ z) ∈ M.U i := (congrArg (fun q : Z ⟶ X => q z ∈ M.U i) h.w).mp hz
      obtain ⟨J, hJ, eJ⟩ := exists_good M hM z (fun _ : PUnit => g₁ ≫ f) (fun _ => i)
        (fun _ _ _ => rfl) (fun _ => hz)
      have v := hv z J hJ
      rw [val_of t g₁ z J (fun _ => i) eJ,
        val_of t g₂ z J (fun _ => i) (fun k => h.w ▸ eJ k)] at v
      exact (gm_res g₁ z _ hz _).trans (v.trans (gm_res g₂ z _ hz₂ _).symm)
  choose a ha using ex
  have ga : ∀ i (y : X'), f y ∈ M.U i →
      gm f y (M.U i) (a i) = gm (𝟙 X') y (LB.wchart M (fun _ : PUnit => f) (fun _ => i)) (t.s fun _ => i) :=
    fun i y hy => by
      have := gm_pull (𝟙 X') f y (M.U i) hy (a i)
      rw [Category.id_comp, ha] at this
      exact this.symm.trans (gm_res (𝟙 X') y (le i) hy _)
  refine ⟨⟨a⟩, fun i j => unit_ext_of_flat f fun y hy => ?_⟩
  have c := gen_trans ht (𝟙 X') y (j := fun _ => i) (j' := fun _ => j) (le i hy.1) (le j hy.2)
  rw [← ga i y hy.1, ← ga j y hy.2, trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  exact (gm_res f y _ hy _).trans (c.trans ((map_mul _ _ _).trans (congrArg _ (gm_res f y _ hy _))).symm)

end GlobalTheory.FlatDescent
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem sum_prod_pow_div_pow {ι S : Type} [Fintype ι] [Fintype S] (m μ : S → ℕ) (x : S → ι → ℂ)
    (ω : ℂ) :
    (∑ i, ∏ s, x s i ^ μ s) / ω ^ (∑ s, μ s * m s) = ∑ i, ∏ s, (x s i / ω ^ m s) ^ μ s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm]

theorem transport_power_sums : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  intro g ι S _ _ act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hfam hq h4 h6 μ
  obtain ⟨-, -, -, -, hpow, -, hprod, -⟩ := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act
  obtain ⟨-, -, -, -, qpow, qfin⟩ := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hM : IsFam act (((∑ s, μ s * m s : ℕ) : ℤ)) fun i τ => ∏ s, f s i τ ^ μ s := by
    have := hprod S Finset.univ (fun s => (μ s : ℤ) * (m s : ℤ)) (fun s i τ => f s i τ ^ μ s)
      (fun s _ => hpow (m s) (f s) (μ s) (hfam s))
    push_cast
    exact this
  have hQ : QConj g N (fun τ => ∑ i, ∏ s, f s i τ ^ μ s) fun τ => ∑ i, ∏ s, f' s i τ ^ μ s :=
    (qfin ι Finset.univ (fun i τ => ∏ s, f s i τ ^ μ s) (fun i τ => ∏ s, f' s i τ ^ μ s)
      fun i _ => (qfin S Finset.univ (fun s τ => f s i τ ^ μ s) (fun s τ => f' s i τ ^ μ s)
        fun s _ => qpow _ _ (μ s) (hq s i)).2).1
  have key := GlobalTheory.T.levelOne_modularForm_value_galois_transport g (∑ s, μ s * m s) N _ _ τ₀ τ₁ ω₀ ω₁ hN
    (fun γ => (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hM γ).1) hQ h4 h6
  rw [sum_prod_pow_div_pow m μ (fun s i => f s i τ₀), sum_prod_pow_div_pow m μ (fun s i => f' s i τ₁)] at key

  simpa only [map_sum, map_prod, map_pow] using key

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)

namespace GlobalTheory.QFam

theorem isIntegral_value_div (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ) (hN : 0 < N) (hact : ActBij act)
    (hf : IsFam act w f) (hq : ∀ i, QAll (· ∈ R) N (f i)) (hj : IsIntegral R (jT τ₀))
    (hΩ : Ω ^ 12 = DD τ₀) (i : ι) : IsIntegral R (f i τ₀ / Ω ^ w) := by
  have hq' : ∀ i, QAll (· ∈ (integralClosure R ℂ).toSubring) N (f i) := fun i => by
    obtain ⟨a, ha, haR⟩ := hq i
    exact ⟨a, ha, fun n => (integralClosure R ℂ).algebraMap_mem ⟨a n, haR n⟩⟩
  have hs := GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring ι act w N f (integralClosure R ℂ).toSubring τ₀ hN hact hf hq' hj
  have h1 : IsIntegral (integralClosure R ℂ) (f i τ₀ ^ 12 / DD τ₀ ^ w) :=
    GlobalTheory.T.isIntegral_of_esymm_mem_subring ι (integralClosure R ℂ).toSubring (fun i => f i τ₀ ^ 12 / DD τ₀ ^ w) hs i
  have h2 : IsIntegral R (f i τ₀ ^ 12 / DD τ₀ ^ w) := isIntegral_trans _ h1
  have h3 : (f i τ₀ / Ω ^ w) ^ 12 = f i τ₀ ^ 12 / DD τ₀ ^ w := by
    rw [div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm]
  exact IsIntegral.of_pow (n := 12) (by norm_num) (h3 ▸ h2)

end GlobalTheory.QFam
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F), psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  first | (exact @GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (exact GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (intros; apply GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  first | exact @GlobalTheory.WpFam.DerivExpansion.main | exact GlobalTheory.WpFam.DerivExpansion.main | (intros; apply GlobalTheory.WpFam.DerivExpansion.main <;> assumption)
end
