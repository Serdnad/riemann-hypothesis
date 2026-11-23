module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import GroundTheory.Brauer.BaseChangeCSA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Mathlib.GroupTheory.Commensurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DblUnitaryBox

section Alg

variable {A α β : Type} [CommRing A] [Fintype β] [DecidableEq β]

end Alg

section Meas

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance (priority := high) measTup : MeasurableSpace (κ → AF F) := borel _

local instance borelTup : BorelSpace (κ → AF F) := ⟨rfl⟩

theorem integrable_normSq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable (fun x => ‖φ x‖ ^ 2) μ :=
  (schA_memLp_two F κ μ hμ φ hφ).integrable_norm_pow two_ne_zero

theorem lintegral_eq_ofReal (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_normSq μ hμ hφ) (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem integral_mul_star_eq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ φ ∈ schA F κ, T φ ∈ schA F κ)
    (hT : ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {φ₁ φ₂ : (κ → AF F) → ℂ}
    (h₁ : φ₁ ∈ schA F κ) (h₂ : φ₂ ∈ schA F κ) :
    ∫ x, T φ₁ x * star (T φ₂ x) ∂μ = ∫ x, φ₁ x * star (φ₂ x) ∂μ := by
  have hn : ∀ φ ∈ schA F κ, ∫ x, ‖T φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := fun φ hφ => by
    have h := hT φ hφ
    rw [lintegral_eq_ofReal μ hμ (hp φ hφ), lintegral_eq_ofReal μ hμ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hm : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∀ c : ℂ, f + c • g ∈ schA F κ := fun f hf g hg c =>
    (schA F κ).add_mem hf ((schA F κ).smul_mem c hg)
  have pol : ∀ (f : (κ → AF F) → ℂ), f ∈ schA F κ →
      ∀ (g : (κ → AF F) → ℂ), g ∈ schA F κ → ∫ x, f x * star (g x) ∂μ =
      (((∫ x, ‖(f + (1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∫ x, ‖(f + (-1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) +
        Complex.I * ((∫ x, ‖(f + Complex.I • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) -
        Complex.I * ((∫ x, ‖(f + (-Complex.I) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ)) / 4 := fun f hf g hg => by
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖(f + c • g) x‖ ^ 2 : ℝ) : ℂ)) μ := fun c =>
      (integrable_normSq μ hμ (hm f hf g hg c)).ofReal
    simp only [← integral_complex_ofReal]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi _) (hi _),
      ← integral_add, ← integral_sub, ← integral_div]
    rotate_left
    · exact ((hi _).sub (hi _)).add ((hi _).const_mul _)
    · exact (hi _).const_mul _
    · exact (hi _).sub (hi _)
    · exact (hi _).const_mul _
    congr 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
      map_add, map_mul, map_neg, map_one, Complex.conj_I, Complex.star_def]
    linear_combination ((f x * (starRingEnd ℂ) (g x)) / 2 - (g x * (starRingEnd ℂ) (f x)) / 2) * Complex.I_mul_I
  rw [pol _ (hp _ h₁) _ (hp _ h₂), pol _ h₁ _ h₂]
  simp only [← hn _ (hm _ h₁ _ h₂ _), map_add (f := _), map_smul]


end Meas

section Shape

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {M : Type} [AddCommGroup M] [Module (AF F) M]
  {Bf : M → M → AF F}

attribute [local instance] measTup borelTup

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Shape

section Lagr

variable {R A α β m κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype α] [DecidableEq α] [Fintype κ]
  {Bf : Matrix α β A → Matrix α β A → R} (co : Darboux Bf κ)



end Lagr

section Value

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] measTup borelTup

end Value

end GlobalTheory.DblUnitaryBox

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PolyArch

theorem roots_eig_any (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C) (w : ℂ)
    (hw : (minpoly G.F γ).eval₂ v.embedding w = 0) : ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v γ *ᵥ x = w • x := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ (γ ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ (γ ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF (γ ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) γ)
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F γ).natDegree => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hd0 : 0 < (minpoly G.F γ).natDegree := minpoly.natDegree_pos hint
  have hpm : (minpoly G.F γ).Monic := minpoly.monic hint
  set Q := (minpoly G.F γ).map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = (minpoly G.F γ).natDegree := by rw [hQ, hpm.natDegree_map]
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF γ) (minpoly G.F γ) = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = (minpoly G.F γ).natDegree - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F γ).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel hd0]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum
    ⟨(minpoly G.F γ).natDegree - 1, by omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKCx.PolyArch

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

open IsDedekindDomain

theorem ratint_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ),
    (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) →
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  intro p hp q h
  have hp' : p.Prime := hp.out
  have key : ∀ {l : ℕ}, l.Prime → l ∣ q.den → l = p := by
    intro l hl hld
    by_contra hne
    have hlI : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    let v : HeightOneSpectrum ℤ :=
      ⟨Ideal.span {(l : ℤ)}, (Ideal.span_singleton_prime hlI.ne_zero).2 hlI, by simpa using hl.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro e
      have h1 : (l : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (by
        have : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
        rw [← e] at this
        exact Ideal.mem_span_singleton.1 this |>.elim (fun c hc => by
          exact Ideal.mem_span_singleton.2 ⟨c, hc⟩))
      have h2 : l ∣ p := Int.natCast_dvd_natCast.1 h1
      exact hne ((Nat.prime_dvd_prime_iff_eq hl hp').1 h2)
    have hq := h ⟨v, hv⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hq
    have hq2 : v.valuation ℚ q ≤ 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hq
    have hb : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_nz
    have hcop : ((q.den : ℤ)) ∈ v.asIdeal → q.num ∉ v.asIdeal := by
      intro hd hn
      have hd' : (l : ℤ) ∣ (q.den : ℤ) := Ideal.mem_span_singleton.1 hd
      have hn' : (l : ℤ) ∣ q.num := Ideal.mem_span_singleton.1 hn
      have hc : IsCoprime q.num (q.den : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast q.reduced
      exact hlI.not_unit (hc.isUnit_of_dvd' hn' hd')
    have e : q = ((algebraMap ℤ ℚ q.num) / (algebraMap ℤ ℚ (q.den : ℤ))) := by
      simp [Rat.num_div_den]
    rw [e, v.valuation_div_le_one_iff ℚ q.num hb hcop] at hq2
    exact hq2 (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 hld))
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hld => key hl hld)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  have : ((p : ℚ) ^ q.den.primeFactorsList.length) = (q.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.den_mul_eq_num]

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAway

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

def intAfP (p : ℕ) : Set (AfP p) :=
  {a | ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem natCast_mem (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  _root_.natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.2 hb0, ?_⟩
  have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (|b|) := by
    rw [← Int.natCast_natAbs, map_natCast]
  rw [e]
  rcases abs_choice b with h | h
  · rw [h, mul_comm]; exact hbx
  · rw [h, map_neg, neg_mul, mul_comm]; exact neg_mem hbx

theorem eval_natCast_mul {p : ℕ} (v : AwayP p) (n : ℕ) (a : AfP p) :
    AfP.eval v ((n : AfP p) * a) = (n : v.1.adicCompletion ℚ) * AfP.eval v a := by
  rw [map_mul, map_natCast]

theorem exists_nat_adele {p : ℕ} (a : AfP p) : ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 (AfP.eval v a)
  have hS : {v : AwayP p | ¬ AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (a : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [eval_natCast_mul]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem w.1 k) (hm w)
  · have hw' : AfP.eval w a ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem w.1 _) hw'

theorem exists_pow_of_integral_away (p : ℕ) [Fact p.Prime] (r : ℚ)
    (h : ∀ v : AwayP p, (v.1.valuation ℚ r) ≤ 1) : ∃ (k : ℤ) (e : ℕ), r * (p : ℚ) ^ e = k := by
  have hden : r.den = p ^ r.den.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd r.den_nz fun {ℓ} hℓ hdvd => ?_
    by_contra hne
    have hℓ' : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
    let v : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)}, (Ideal.span_singleton_prime hℓ'.ne_zero).2 hℓ',
      by simpa using hℓ.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro h'
      have h'' : Associated (ℓ : ℤ) (p : ℤ) := Ideal.span_singleton_eq_span_singleton.1 h'
      exact hne (by simpa using Int.natAbs_eq_iff_associated.2 h'')
    have h1 := Rat.valuation_le_one_iff_den.1 (h ⟨v, hv⟩)
    exact h1 (Ideal.mem_span_singleton.2 (by exact_mod_cast hdvd))
  refine ⟨r.num, r.den.primeFactorsList.length, ?_⟩
  have : ((p : ℚ) ^ r.den.primeFactorsList.length) = (r.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.mul_den_eq_num]

theorem den_bounded_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Ω : Set (AfP p)), IsCompact Ω → ∃ M : ℕ, 0 < M ∧
    ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Ω → ∃ (k : ℤ) (e : ℕ), q * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  intro p _ Ω hΩ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun q hq => ?_⟩
  obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (ht hq)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hqa' : (m a : AfP p) * algebraMap ℚ (AfP p) q ∈ intAfP p := hqa
  have hint : ∀ v : AwayP p, v.1.valuation ℚ (((∏ a ∈ t, m a : ℕ) : ℚ) * q) ≤ 1 := by
    intro v
    have h2 : AfP.eval v (algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q)) ∈
        v.1.adicCompletionIntegers ℚ := by
      have e : algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q) =
          (k : AfP p) * ((m a : AfP p) * algebraMap ℚ (AfP p) q) := by
        rw [map_mul, map_natCast, hk, Nat.cast_mul]; ring
      rw [e, eval_natCast_mul]
      exact mul_mem (natCast_mem v.1 k) (hqa' v)
    rw [AlgHom.commutes] at h2
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    exact h2
  obtain ⟨z, e, hz⟩ := exists_pow_of_integral_away p _ hint
  exact ⟨z, e, by rw [← hz]; ring⟩

end GlobalTheory.DenAway
end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AwayOrb

variable {p : ℕ} [Fact p.Prime]

def compL (G : HTGroup p) (w : AwayP p) : G.GAf →* UPts G.star (w.1.adicCompletion ℚ) :=
  ubcMap (AfP.eval w)

def coordL (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) :
    Fin (Module.finrank ℚ G.C) → w.1.adicCompletion ℚ :=
  (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr a

def intPts (G : HTGroup p) (w : AwayP p) : Set (UPts G.star (w.1.adicCompletion ℚ)) :=
  {h | (∀ i, coordL G w (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (∀ i, coordL G w ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1)⁻¹ :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2 : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ ∧
      ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2)⁻¹ : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ}

end GlobalTheory.AwayOrb
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.hermitian_congr_of_positiveIndex_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian), A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB → ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  first | exact @GlobalTheory.HermCongruence.congr_of_sigPosH_eq | exact GlobalTheory.HermCongruence.congr_of_sigPosH_eq | (intros; apply GlobalTheory.HermCongruence.congr_of_sigPosH_eq <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.hermitianForm_neg_on_orthogonal_of_positiveIndex_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  first | exact @GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | (intros; apply GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.negDef_of_hermitianMatrixPositiveIndex_eq_zero : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 0 → ∀ y : Fin n → ℂ, y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  first | (exact @GlobalTheory.herm_negDef_of_sigPosH_eq_zero) | (exact GlobalTheory.herm_negDef_of_sigPosH_eq_zero) | (intros; apply GlobalTheory.herm_negDef_of_sigPosH_eq_zero  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.compactOpenLevel_conj_commensurable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (g : G.GAf), Subgroup.Commensurable (L.K.toSubgroup.map (MulAut.conj g).toMonoidHom) L.K.toSubgroup := by
  first | (exact @GlobalTheory.LKMid.level_conj_commensurable) | (exact GlobalTheory.LKMid.level_conj_commensurable) | (intros; apply GlobalTheory.LKMid.level_conj_commensurable  <;> assumption)
end
