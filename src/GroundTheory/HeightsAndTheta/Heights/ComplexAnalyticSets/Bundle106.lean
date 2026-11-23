module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets FieldNumbers

noncomputable section

theorem exists_finset_span_integral_of_div (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O Ω : Type}
    [CommRing O] [Field Ω] [Algebra O Ω] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f)
    (hΩ : ∀ x : Ω, ∃ a b : O, x = algebraMap O Ω a / algebraMap O Ω b) :
    ∃ t : Finset Ω, ∀ x : Ω, IsIntegral O x → x ∈ Submodule.span O (t : Set Ω) := by
  let ψ : MvPolynomial (Fin n) ℂ →+* Ω := (algebraMap O Ω).comp φ
  let _ : Algebra ℂ Ω := (ψ.comp C).toAlgebra
  let S : Set Ω := Set.range fun i ↦ ψ (X i)
  have hpoly : ∀ f, ψ f ∈ Algebra.adjoin ℂ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f i hf => rw [map_mul]; exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  let A : Subalgebra ℂ Ω :=
    { toSubsemiring := (algebraMap O Ω).rangeS, algebraMap_mem' := fun c ↦ ⟨φ (C c), rfl⟩ }
  have hRA : Algebra.adjoin ℂ S ≤ A := Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨φ (X i), rfl⟩)
  have hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin ℂ S, ∃ d ∈ Algebra.adjoin ℂ S, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹ := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨f, s, hs, ho⟩ := hφ o
    refine ⟨ψ f, hpoly f, ψ s, hpoly s, (hs.map (algebraMap O Ω)).ne_zero, ⟨↑hs.unit⁻¹, ?_⟩, ?_⟩
    · change algebraMap O Ω ↑hs.unit⁻¹ = (algebraMap O Ω (φ s))⁻¹
      rw [map_units_inv, IsUnit.unit_spec]
    · refine (eq_mul_inv_iff_mul_eq₀ (hs.map (algebraMap O Ω)).ne_zero).2 ?_
      change algebraMap O Ω o * algebraMap O Ω (φ s) = algebraMap O Ω (φ f)
      rw [← map_mul, ho]
  have hE : ∀ x : Ω, x ∈ IntermediateField.adjoin ℂ S := by
    have hA : ∀ a ∈ A, a ∈ IntermediateField.adjoin ℂ S := by
      intro a ha
      obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
      exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hr)
        (inv_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hd))
    intro x
    obtain ⟨a, b, rfl⟩ := hΩ x
    exact div_mem (hA _ ⟨a, rfl⟩) (hA _ ⟨b, rfl⟩)
  have hfin : FiniteDimensional (IntermediateField.adjoin ℂ S)
      (IntermediateField.extendScalars (le_refl (IntermediateField.adjoin ℂ S))) := by
    rw [IntermediateField.extendScalars_self]; infer_instance
  obtain ⟨t, -, ht⟩ := exists_finset_integral_span hN (Set.finite_range _) A _ hRA hloc le_rfl hfin
  let _ : Algebra O A := ((algebraMap O Ω).codRestrict A fun o ↦ (⟨o, rfl⟩ : algebraMap O Ω o ∈ (algebraMap O Ω).rangeS)).toAlgebra
  have : IsScalarTower O A Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsur : Function.Surjective (algebraMap O A) := by rintro ⟨_, o, rfl⟩; exact ⟨o, rfl⟩
  refine ⟨t, fun x hx ↦ ?_⟩
  rw [← Submodule.restrictScalars_span O A hsur]
  exact ht x (hE x) hx.tower_top

theorem exists_algHom_span_of_mem_minimalPrimes (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ}
    {O : Type} [CommRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) {p : Ideal O} (hp : p ∈ minimalPrimes O) :
    ∃ g : FractionRing O →ₐ[O] FractionRing (O ⧸ p), ∃ t : Finset (FractionRing (O ⧸ p)),
      ∀ x : FractionRing O, IsIntegral O x → g x ∈ Submodule.span O (t : Set (FractionRing (O ⧸ p))) := by
  have := Ideal.IsMinimalPrime.isPrime hp
  have hu : ∀ y : nonZeroDivisors O, IsUnit (Algebra.ofId O (FractionRing (O ⧸ p)) y) := by
    intro y
    refine IsUnit.mk0 _ fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ?_ hp y.2
    have h' : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p y) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by rw [map_zero]; exact h
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ h')
  obtain ⟨t, ht⟩ := exists_finset_span_integral_of_div hN φ hφ (Ω := FractionRing (O ⧸ p)) fun x ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O ⧸ p) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩
  exact ⟨IsLocalization.liftAlgHom (M := nonZeroDivisors O) hu, t, fun x hx ↦ ht _ (hx.map _)⟩

theorem finite_integralClosure_of_isReduced (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O : Type}
    [CommRing O] [IsReduced O] [IsNoetherianRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) :
    Module.Finite O (integralClosure O (FractionRing O)) := by
  have := (minimalPrimes.finite_of_isNoetherianRing O).to_subtype
  choose g t ht using fun p : minimalPrimes O ↦ exists_algHom_span_of_mem_minimalPrimes hN φ hφ p.2
  let F : integralClosure O (FractionRing O) →ₗ[O]
      ((p : minimalPrimes O) → Submodule.span O (t p : Set (FractionRing (O ⧸ (p : Ideal O))))) :=
    LinearMap.pi fun p ↦ LinearMap.codRestrict _
      ((g p).toLinearMap ∘ₗ (integralClosure O (FractionRing O)).val.toLinearMap) fun x ↦ ht p x x.2
  refine Module.Finite.of_injective F ((injective_iff_map_eq_zero F).2 fun x hx ↦ ?_)
  have h0 : ∀ p : minimalPrimes O, g p x = 0 := fun p ↦ congrArg Subtype.val (congr_fun hx p)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) (x : FractionRing O)
  have ha : a ∈ sInf (minimalPrimes O) := by
    refine Ideal.mem_sInf.2 fun p hp ↦ ?_
    have := Ideal.IsMinimalPrime.isPrime hp
    have e : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p a) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by
      rw [map_zero]
      change algebraMap O (FractionRing (O ⧸ p)) a = 0
      rw [← (g ⟨p, hp⟩).commutes, ← hab, map_mul, h0, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ e)
  rw [Ideal.sInf_minimalPrimes, Ideal.mem_radical_iff] at ha
  obtain ⟨k, hk⟩ := ha
  have ha0 : a = 0 := IsNilpotent.eq_zero ⟨k, by simpa using hk⟩
  rw [ha0, map_zero, (IsLocalization.map_units (FractionRing O) b).mul_left_eq_zero] at hab
  exact Subtype.ext hab

theorem isReduced_curveLocalRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (h : IsRadicalAt I q) : IsReduced (curveLocalRing I q) := by
  refine (Ideal.isRadical_iff_quotient_reduced _).1 ?_
  rw [Ideal.IsRadical, ← IsLocalization.map_radical (RingHom.ker (eval q)).primeCompl]
  refine Ideal.map_le_iff_le_comap.2 fun f hf ↦ ?_
  obtain ⟨s, hs, hsf⟩ := h f hf
  have hu : IsUnit (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) s) :=
    IsLocalization.map_units _ (⟨s, fun h' ↦ hs (RingHom.mem_ker.1 h')⟩ : (RingHom.ker (eval q)).primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).1 (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ hsf)

theorem curveLocalRing_eq_div {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (o : curveLocalRing I q) : ∃ f s, IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s) ∧
      o * algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s =
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
  obtain ⟨z, rfl⟩ : ∃ z, Ideal.Quotient.mk
      (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))) z = o :=
    Ideal.Quotient.mk_surjective o
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl z
  refine ⟨f, s, isUnit_algebraMap_curveLocalRing I q s fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have e := congrArg (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval q))) f s)
  rw [map_mul] at e
  exact e

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetFormComparison

theorem hessC_congr {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    hessC f y = hessC g y := by
  unfold hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

theorem contDiff_logPot (N : ℕ) : ContDiff ℝ ∞ (HilbertSamuel.ProjFS.logPot (N := N)) := by
  have h : (HilbertSamuel.ProjFS.logPot (N := N)) = fun z => Real.log (1 + euclPot z) := rfl
  rw [h]
  exact (contDiff_const.add (contDiff_euclPot N)).log fun z => by
    have : 0 ≤ euclPot z := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith

theorem posSemidef_hessC_logPot_sub {N : ℕ} {z : Fin N → ℂ} (hz : ‖z‖ ≤ 1) :
    ((((1 + N : ℝ) ^ 2 : ℝ) : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1).PosSemidef := by
  set m : ℝ := (1 + N) ^ 2 with hm
  have h1 : ContDiffAt ℝ 2 (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w) z :=
    contDiffAt_const.mul (((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have h2 : ContDiffAt ℝ 2 (fun w => (-1 : ℝ) * euclPot w) z :=
    contDiffAt_const.mul (((contDiff_euclPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have e : (m : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1 =
      hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z := by
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ z h1 h2, ReciprocityTheory.AnForm.M.hessC_const_mul',
      ReciprocityTheory.AnForm.M.hessC_const_mul', TubeFormComparison.hessC_euclPot]
    simp [sub_eq_add_neg]
  rw [e]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ z (h1.add h2) fun w => ?_
  have hq := ReciprocityTheory.AnForm.M.re_star_dot_hessC
    (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z (star w)
  have hq' : levi (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z w =
      (star (star w) ⬝ᵥ (hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z
        *ᵥ star w)).re := by rw [hq, star_star]
  rw [hq', ← e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, HilbertSamuel.ProjFS.hessC_logPot_eq_chernCoeff 0, Matrix.smul_mulVec,
    dotProduct_smul, CP.chernCoeff_quadForm, CP.star_dotProduct_self]
  set a : ℝ := ∑ j, ‖(star w) j‖ ^ 2 with ha
  set q : ℝ := 1 + normSqSum z with hqdef
  have hS0 : 0 ≤ normSqSum z := normSqSum_nonneg z
  have hSN : normSqSum z ≤ N := by
    have : ∀ j, ‖z j‖ ^ 2 ≤ 1 := fun j =>
      pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm z j).trans hz)
    calc normSqSum z = ∑ j, ‖z j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin N, (1 : ℝ) := Finset.sum_le_sum fun j _ => this j
      _ = N := by simp
  have hCS := CP.norm_dotProduct_sq_le z (star w)
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq1 : 1 ≤ q := by linarith
  have hpi := Real.pi_pos
  have hval : ((m : ℂ) • (((2 * Real.pi : ℝ) : ℂ) • ((1 / (2 * Real.pi * q) *
      (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) : ℝ) : ℂ)) - (a : ℂ)).re =
      m * (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) / q - a := by
    simp only [smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
    field_simp
  rw [hval]
  rw [← ha] at hCS
  have hd : q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 ≤ (1 - q⁻¹) * a := by
    rw [inv_mul_le_iff₀ (by linarith)]
    have : q * ((1 - q⁻¹) * a) = normSqSum z * a := by
      rw [hqdef]
      field_simp
      ring
    rw [this]
    exact hCS
  have hqm : q ^ 2 ≤ m := by
    rw [hm]
    have : q ≤ 1 + N := by linarith
    exact pow_le_pow_left₀ (by linarith) this 2
  have hqa : a / q ≤ a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 := by
    have : a / q = q⁻¹ * a := by ring
    nlinarith
  rw [sub_nonneg, le_div_iff₀ (by linarith)]
  have h4 : q ^ 2 * (a / q) = q * a := by
    field_simp
  nlinarith [h4, mul_le_mul_of_nonneg_left hqa (by positivity : (0 : ℝ) ≤ m),
    mul_le_mul_of_nonneg_right hqm (div_nonneg ha0 (by linarith : (0 : ℝ) ≤ q))]

end SheetFormComparison


end

end GroundTheory.Heights₂.Heights
end
