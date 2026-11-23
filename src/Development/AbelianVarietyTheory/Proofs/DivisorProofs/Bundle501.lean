module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
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
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.HeckeLBound

variable {E : Type} [Field E] [NumberField E]

def ratPrime (v : HeightOneSpectrum (𝓞 E)) : ℕ := Ideal.absNorm (v.asIdeal.under ℤ)

theorem ratPrime_prime (v : HeightOneSpectrum (𝓞 E)) : (ratPrime v).Prime := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  exact Nat.absNorm_under_prime v.asIdeal

theorem absNorm_eq_ratPrime_pow (v : HeightOneSpectrum (𝓞 E)) : ∃ f : ℕ, Ideal.absNorm v.asIdeal = ratPrime v ^ f :=
  have : v.asIdeal.LiesOver (Ideal.span {((ratPrime v : ℕ) : ℤ)}) := Int.liesOver_span_absNorm v.asIdeal
  ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal (ratPrime_prime v)⟩

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 E)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem ratPrime_le_absNorm (v : HeightOneSpectrum (𝓞 E)) : ratPrime v ≤ Ideal.absNorm v.asIdeal := by
  obtain ⟨f, hf⟩ := absNorm_eq_ratPrime_pow v
  have h2 := two_le_absNorm v
  have hp := ratPrime_prime v
  rw [hf] at h2 ⊢
  have hf0 : f ≠ 0 := by rintro rfl; simp at h2
  calc ratPrime v = ratPrime v ^ 1 := (pow_one _).symm
    _ ≤ ratPrime v ^ f := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.2 hf0)

theorem mem_primesOverFinset_ratPrime (v : HeightOneSpectrum (𝓞 E)) :
    v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((ratPrime v : ℕ) : ℤ)}) (𝓞 E) := by
  have hp := ratPrime_prime v
  have : (Ideal.span {((ratPrime v : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  rw [IsDedekindDomain.mem_primesOverFinset_iff (by simp [hp.ne_zero])]
  exact ⟨v.isPrime, Int.liesOver_span_absNorm v.asIdeal⟩

theorem card_filter_ratPrime_le (u : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) (hp : p.Prime) :
    (u.filter fun x => ratPrime x = p).card ≤ Module.finrank ℚ E := by
  classical
  have : (Ideal.span {(p:ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  refine le_trans ?_ (Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E (p := Ideal.span {(p:ℤ)}) (by simp [hp.ne_zero]))
  refine Finset.card_le_card_of_injOn (fun x => x.asIdeal) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter] at hx
    have := mem_primesOverFinset_ratPrime x
    rw [hx.2] at this
    exact this
  · intro x _ y _ hxy
    exact HeightOneSpectrum.ext hxy

def fac (x : ℝ) : ℝ := (1 - x ^ (-(3 / 2 : ℝ)))⁻¹

theorem one_sub_rpow_neg_three_halves_mem_Ioc {x : ℝ} (hx : 2 ≤ x) : 0 < 1 - x ^ (-(3 / 2 : ℝ)) ∧ 1 - x ^ (-(3 / 2 : ℝ)) ≤ 1 := by
  have h1 : x ^ (-(3 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have h2 : 0 < x ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  constructor <;> linarith

theorem one_le_fac {x : ℝ} (hx : 2 ≤ x) : 1 ≤ fac x := by
  obtain ⟨h1, h2⟩ := one_sub_rpow_neg_three_halves_mem_Ioc hx
  exact one_le_inv₀ h1 |>.2 h2

theorem fac_anti {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : fac y ≤ fac x := by
  obtain ⟨h1, _⟩ := one_sub_rpow_neg_three_halves_mem_Ioc hx
  unfold fac
  apply inv_anti₀ h1
  have : y ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by norm_num)
  linarith

end GlobalTheory.HeckeLBound

noncomputable section

namespace GlobalTheory.HeckeLBound

variable {E : Type} [Field E] [NumberField E]

open Filter Topology

theorem norm_val_eq_one {χ : HChar E} (hU : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := by
  rw [← finPart_unifAt]
  exact hU _

theorem norm_eulerFactor_le {χ : HChar E} (hU : IsUnitary χ) {s : ℂ} (hs : 3 / 2 ≤ s.re) (v : HeightOneSpectrum (𝓞 E)) :
    ‖eulerFactor χ s v‖ ≤ fac (Ideal.absNorm v.asIdeal : ℝ) := by
  have hN : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v
  obtain ⟨h1, h2⟩ := one_sub_rpow_neg_three_halves_mem_Ioc hN
  unfold eulerFactor
  split_ifs with h
  · have hpos : 0 < Ideal.absNorm v.asIdeal := by have := two_le_absNorm v; omega
    have hc : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hpos]; simp
    have hle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hlow : 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        ‖1 - ((χ.val v : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (((χ.val v : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
      rw [norm_mul, norm_val_eq_one hU, hc, norm_one] at this
      linarith
    rw [norm_inv]
    exact inv_anti₀ h1 hlow
  · rw [norm_one]; exact one_le_fac hN

theorem prod_fac_le_zeta (T : Finset Nat.Primes) : ∏ p ∈ T, fac ((p : ℕ) : ℝ) ≤ ‖riemannZeta (3 / 2)‖ := by
  have h := riemannZeta_eulerProduct_hasProd (s := 3 / 2) (by norm_num)
  have hf : (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(3 / 2 : ℂ)))⁻¹) = fun p : Nat.Primes => ((fac ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
    funext p
    unfold fac
    rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  rw [hf] at h
  have h' : Tendsto (fun T : Finset Nat.Primes => ∏ p ∈ T, fac ((p : ℕ) : ℝ)) atTop (𝓝 ‖riemannZeta (3 / 2)‖) := by
    have := (continuous_norm.tendsto _).comp h
    refine this.congr fun T => ?_
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_prod, Complex.norm_of_nonneg]
    exact Finset.prod_nonneg fun p _ => le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le))
  refine ge_of_tendsto h' ?_
  filter_upwards [Filter.eventually_ge_atTop T] with T' hT
  rw [← Finset.prod_sdiff hT]
  have h1 : 1 ≤ ∏ p ∈ T' \ T, fac ((p : ℕ) : ℝ) :=
    by simpa using Finset.prod_le_prod₀ (s := T' \ T) (f := fun _ => (1:ℝ)) (fun _ _ => zero_le_one) (fun p _ => one_le_fac (by exact_mod_cast p.2.two_le))
  have h0 : 0 ≤ ∏ p ∈ T, fac ((p : ℕ) : ℝ) :=
    Finset.prod_nonneg fun p _ => le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le))
  nlinarith

end GlobalTheory.HeckeLBound

noncomputable section

namespace GlobalTheory.HeckeLBound

variable {E : Type} [Field E] [NumberField E]

open Filter Topology

theorem prod_fac_absNorm_le (F : Finset (HeightOneSpectrum (𝓞 E))) :
    ∏ v ∈ F, fac (Ideal.absNorm v.asIdeal : ℝ) ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  classical
  let g : HeightOneSpectrum (𝓞 E) → Nat.Primes := fun v => ⟨ratPrime v, ratPrime_prime v⟩
  have hg2 : ∀ v, (2 : ℝ) ≤ ((g v : ℕ) : ℝ) := fun v => by exact_mod_cast (ratPrime_prime v).two_le
  have step1 : ∏ v ∈ F, fac (Ideal.absNorm v.asIdeal : ℝ) ≤ ∏ v ∈ F, fac ((g v : ℕ) : ℝ) :=
    Finset.prod_le_prod₀ (fun v _ => le_trans zero_le_one (one_le_fac (le_trans (hg2 v) (by exact_mod_cast ratPrime_le_absNorm v))))
      (fun v _ => fac_anti (hg2 v) (by exact_mod_cast ratPrime_le_absNorm v))
  rw [Finset.prod_comp (fun p : Nat.Primes => fac ((p : ℕ) : ℝ)) g] at step1
  refine le_trans step1 (le_trans (Finset.prod_le_prod₀ (g := fun p : Nat.Primes => fac ((p : ℕ) : ℝ) ^ Module.finrank ℚ E) (fun p _ => ?_) (fun p _ => ?_)) ?_)
  · exact pow_nonneg (le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le))) _
  · refine pow_le_pow_right₀ (one_le_fac (by exact_mod_cast p.2.two_le)) ?_
    have : (F.filter fun v => g v = p) = F.filter fun v => ratPrime v = (p : ℕ) := by
      apply Finset.filter_congr
      intro v _
      exact Subtype.ext_iff
    rw [this]
    exact card_filter_ratPrime_le F p p.2
  · rw [Finset.prod_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun p _ => le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le)))
      (prod_fac_le_zeta _) _

theorem norm_heckeL_le (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ) :
    IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  intro hU hL hS
  have h := hL.2 S (by linarith)
  have h' := (continuous_norm.tendsto _).comp h
  refine le_of_tendsto' h' fun F => ?_
  simp only [Function.comp_apply]
  refine le_trans (Finset.norm_prod_le _ _) (le_trans ?_ (prod_fac_absNorm_le F))
  exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => norm_eulerFactor_le hU hS v)

end GlobalTheory.HeckeLBound
end
end
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.HatCap

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral :
    IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))

theorem mem_orderC_of_mem_hatO {c : Ideal (OF E)} (hc : c ≠ ⊥) {x : E} (hx : algebraMap E (Af E) x ∈ hatO c) :
    x ∈ orderC c := by
  obtain ⟨n, hnc, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have hnE : algebraMap (OF E) E n ≠ 0 := by
    intro h
    apply hn0
    have h' : ((n : maximalRealSubfield E) : E) = 0 := h
    exact_mod_cast h'
  set m : E := algebraMap (OF E) E n with hm
  have hcont : Continuous fun z : Af E => (algebraMap E (Af E) x - z) * algebraMap E (Af E) m⁻¹ :=
    (continuous_const.sub continuous_id).mul continuous_const
  have hU := isOpen_integral.preimage hcont
  obtain ⟨_, hz, y, hy, rfl⟩ := mem_closure_iff.1 hx _ hU (by
    rw [Set.mem_preimage, sub_self, zero_mul]
    exact fun v => zero_mem _)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = (x - y) * m⁻¹ := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
    have h3 : (algebraMap E (Af E) ((x - y) * m⁻¹)) v ∈ v.adicCompletionIntegers E := by
      rw [map_mul, map_sub]; exact hz v
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)
  have hxy : x = y + algebraMap (𝓞 E) E (b * algebraMap (OF E) (𝓞 E) n) := by
    have : algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) n) = m := rfl
    rw [map_mul, hb, this, mul_assoc, inv_mul_cancel₀ hnE]; ring
  rw [hxy]
  refine add_mem hy (mem_orderC.2 ⟨0, _, Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem _ hnc), by simp⟩)

theorem lattice_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  intro E _ _ _ c hc
  ext x
  rw [mem_lattice, inv_one, Units.val_one, mul_one]
  exact ⟨mem_orderC_of_mem_hatO hc, algebraMap_mem_hatO⟩

end GlobalTheory.CMVal.HatCap
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.OpLin

variable {R : Type} [CommRing R]

theorem degree_eq_one {σ : Type} [Fintype σ] {D : σ →₀ ℕ} (h : D.degree = 1) :
    ∃ s, D = Finsupp.single s 1 := by
  classical
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

theorem le_order_prod_pow {σ τ : Type} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (D : σ →₀ ℕ) :
    (D.degree : ℕ∞) ≤ (D.prod fun s e => a s ^ e).order := by
  refine le_trans ?_ (le_order_prod _ _)
  rw [Finsupp.degree_apply, Nat.cast_sum]
  exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (ha s)

theorem coeff_subst_of_degree_le_one {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0)
    {β : τ →₀ ℕ} (hβ : β.degree ≤ 1) :
    coeff β (subst a f) = ∑ s, coeff (Finsupp.single s 1) f * coeff β (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hs]
  have hsupp : (Function.support fun D : σ →₀ ℕ =>
      coeff D f • coeff β (D.prod fun s e => a s ^ e)) ⊆
      ((Finset.univ.image fun s : σ => Finsupp.single s 1 : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ)) := by
    intro D hD
    rw [Function.mem_support] at hD
    have h0 : D ≠ 0 := by
      rintro rfl
      apply hD
      rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    have h1 : D.degree ≤ 1 := by
      by_contra hlt
      push_neg at hlt
      apply hD
      rw [coeff_of_lt_order (lt_of_lt_of_le ?_ (le_order_prod_pow ha D)), smul_zero]
      exact_mod_cast lt_of_le_of_lt hβ hlt
    have h2 : D.degree = 1 := by
      have : D.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff D).1 h)
      omega
    obtain ⟨s, rfl⟩ := degree_eq_one h2
    simp
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun s _ t _ h => Finsupp.single_left_injective one_ne_zero h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_single_index (by simp), pow_one, smul_eq_mul]

end GlobalTheory.QLog.OpLin

namespace GlobalTheory.QLog.OpLin

variable {B O : Type} [CommRing B] [CommRing O] {d : ℕ}

theorem coeff_inl {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single j 1)) (congrFun hμ.unit i)
  simp only [op, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero, eq_comm] using h

theorem coeff_inr {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  rw [← h, ← coeff_inl hμ i j]
  simp [coeff_X, Finsupp.single_left_inj one_ne_zero]

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type}
    (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) →
    (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 →
    coeff β (op μ u v i) = coeff β (u i + v i) := by
  intro B O _ _ θ d μ hμ τ u v hu hv i β hβ
  classical
  simp only [op, at2]
  rw [coeff_subst_of_degree_le_one (by rintro (s | s); exacts [hu s, hv s]) (hμ.const i) hβ,
    Fintype.sum_sum_type, map_add]
  simp [coeff_inl hμ, coeff_inr hμ]

end GlobalTheory.QLog.OpLin
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem Chart.ev_mem_ideal_smul_add_p (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) :
    (∀ α, coeff α h ∈ I) → ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n,
      c.ev n h = a + (p : G.A n) * b := by
  intro hI
  classical
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  let S : Finset (Fin d →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => N)
  let h₁ : MvPowerSeries (Fin d) O := ∑ α ∈ S, monomial α (coeff α h)
  have hmon : ∀ α, (monomial α (coeff α h) : MvPowerSeries (Fin d) O) =
      coeff α h • monomial α (1 : O) := by
    intro α
    ext β
    simp only [coeff_monomial, coeff_smul]
    split_ifs <;> simp
  have hcoeff : ∀ β ∈ S, coeff β h₁ = coeff β h := by
    intro β hβ

    simp only [h₁, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem β hβ]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
  have h₂ : (p : G.A n) ^ 1 ∣ c.ev n (h - h₁) := by
    apply hN
    intro β hβ
    have hmem : β ∈ S := by
      simp only [S, Finset.mem_Iic]
      intro i
      show β i ≤ N
      have : β i ≤ β.degree := by
        by_cases h0 : β i = 0
        · omega
        rw [Finsupp.degree]
        exact Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _)
          (by simpa using h0)
      omega
    rw [map_sub, hcoeff β hmem, sub_self]
  obtain ⟨b, hb⟩ := h₂
  refine ⟨c.ev n h₁, ?_, b, ?_⟩

  · simp only [h₁, map_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [hmon, map_smul]
    exact Submodule.smul_mem_smul (hI α) Submodule.mem_top
  · rw [map_sub, pow_one] at hb
    rw [← hb]; ring

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem series_in_ideal_iff_image :
    ∀ (B Q σ : Type) [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) (f : MvPowerSeries σ Q),
      (In N f ↔ ∃ s : MvPowerSeries σ B, (∀ α, coeff α s ∈ N) ∧ map (algebraMap B Q) s = f) ∧
      ∀ g : MvPowerSeries σ Q, In N f → In N g → ∀ a : B,
        In N (f + algebraMap B Q a • g) ∧ In N (f - g) := by
  intro B Q σ _ _ _ N f
  refine ⟨⟨fun h => ?_, fun ⟨s, hs, hsf⟩ α => ?_⟩, fun g hf hg a => ⟨fun α => ?_, fun α => ?_⟩⟩
  · choose b hbN hb using h
    obtain ⟨s, hs⟩ : ∃ s : MvPowerSeries σ B, ∀ α, coeff α s = b α := ⟨b, fun _ => rfl⟩
    refine ⟨s, fun α => (hs α).symm ▸ hbN α, ?_⟩
    ext α
    rw [coeff_map, hs]
    exact (hb α).symm
  · exact ⟨coeff α s, hs α, by rw [← hsf, coeff_map]⟩
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    refine ⟨b₁ + a * b₂, N.add_mem hb₁N (N.mul_mem_left a hb₂N), ?_⟩
    rw [map_add (f := _), map_smul, smul_eq_mul, hb₁, hb₂, map_add (f := _), map_mul]
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    exact ⟨b₁ - b₂, N.sub_mem hb₁N hb₂N, by rw [map_sub, hb₁, hb₂, map_sub]⟩

end GlobalTheory
end
