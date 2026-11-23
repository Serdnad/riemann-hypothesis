module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Mathlib.RingTheory.LaurentSeries
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.IntermediateValue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem finite_quotient_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (n : ℕ) : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n}) := by
  have h : Ideal.span {((l : ℕ) : O) ^ n} =
      (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O) := by
    simp [Ideal.map_span]
  rw [h]
  haveI : Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}) := by
    rw [← PadicInt.ker_toZModPow]
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow (p := l) n))
  haveI : Module.Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})
      (O ⧸ (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  exact Module.finite_of_finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})

theorem isOpen_integers (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    IsOpen (Set.range (algebraMap ↥(OL LL) ↥LL.1)) := by
  have h : Set.range (algebraMap ↥(OL LL) ↥LL.1) =
      (fun x : ↥LL.1 => (x : PadicAlgCl l)) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    rw [Set.mem_preimage, mem_closedBall_zero_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

theorem good_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) ∧ ∀ n : ℕ, Finite (↥(OL LL) ⧸ Ideal.span {((l : ℕ) : ↥(OL LL)) ^ n}) := by
  intro l _ LL
  haveI := LL.2
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := finite_integralClosure_padicInt l ↥LL.1
  haveI : ContinuousSMul ℚ_[l] ↥LL.1 :=
    Topology.IsInducing.continuousSMul (f := id) (g := fun x : ↥LL.1 => (x : PadicAlgCl l))
      Topology.IsInducing.subtypeVal continuous_id rfl
  haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  refine ⟨⟨⟨inferInstance, isDiscreteValuationRing_integralClosure_padicInt l ↥LL.1,
    isFractionRing_integralClosure_padicInt l ↥LL.1⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, isOpen_integers l LL⟩, finite_quotient_pow l _⟩

end GlobalTheory.LocalIntegers
end

section

open Matrix

namespace GlobalTheory.UnitDiscAlg

section Basic
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem integ_mul {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x * y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun k _ => by rw [norm_mul]; exact mul_le_one₀ (hx i k) (norm_nonneg _) (hy k j))

theorem integ_add {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x + y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (hy i j))

theorem integ_sub {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x - y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (by rw [norm_neg]; exact hy i j))

theorem integ_one : ∀ i j, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem integ_zero : ∀ i j, ‖(0 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  simp

theorem integ_pow {x : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (k : ℕ) :
    ∀ i j, ‖(x ^ k) i j‖ ≤ 1 := by
  induction k with
  | zero => simpa using integ_one
  | succ k ih => rw [pow_succ]; exact integ_mul ih hx

theorem integ_smul {x : Matrix (Fin n) (Fin n) E} {a : E} (ha : ‖a‖ ≤ 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ∀ i j, ‖(a • x) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i j)

end Basic

theorem comm_of_bezout {E : Type} [Field E] {n : ℕ} {N a b : Matrix (Fin n) (Fin n) E}
    (h : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (ha : a * N = N * a) (hb : b * N = N * b) : a * b = b * a := by
  obtain ⟨u, v, huv⟩ := h
  have hs : N.charpoly.Separable := ⟨u, v, huv⟩
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.cyclicField E (Fin n) N hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N w hw).2.2
  have ha' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij ha
  have hb' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij hb
  exact congrArg Subtype.val
    (mul_comm (⟨a, ha'⟩ : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg N) ⟨b, hb'⟩)

end GlobalTheory.UnitDiscAlg
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory

theorem orbit_class_trivial : ∀ (o : ℕ) (p : ℝ) (f : ℕ → ℝ → ℝ), 0 < o → 1 < p → (∀ i, ContinuousOn (f i) (Set.Ioc 0 1)) → (∀ i, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ f i r) → (∀ i j, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < f i r → 0 < f j r → i % o = j % o) → (∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ i, 0 < f i r) → (∀ i r, 0 < r → r ≤ 1 / p → 0 < f i r → 0 < f (i + 1) (p * r)) → o = 1 := by
  intro o p f _ho hp hc _ hcl hcov hsh
  classical
  let g : ℝ → ℕ := fun r => if h : ∃ i, 0 < f i r then (Classical.choose h) % o else 0
  have hg : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, 0 < f i r → g r = i % o := by
    intro r hr i hi
    have h : ∃ i, 0 < f i r := ⟨i, hi⟩
    simp only [g, dif_pos h]
    exact hcl _ _ r hr (Classical.choose_spec h) hi
  have gcont : ContinuousOn g (Set.Ioc (0 : ℝ) 1) := by
    intro r hr
    obtain ⟨i, hi⟩ := hcov r hr
    rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
    have h1 : ∀ᶠ x in nhdsWithin r (Set.Ioc (0 : ℝ) 1), 0 < f i x :=
      ((hc i) r hr).eventually (lt_mem_nhds hi)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxs
    rw [hg x hxs i hx, hg r hr i hi]
  have hp0 : 0 < p := by linarith
  have hr1 : 1 / p ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hp0]; exact hp.le⟩
  have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hconst : g (1 / p) = g 1 := isPreconnected_Ioc.constant gcont hr1 h1
  obtain ⟨i, hi⟩ := hcov (1 / p) hr1
  have hi1 : 0 < f (i + 1) 1 := by
    have := hsh i (1 / p) (by positivity) le_rfl hi
    rwa [mul_one_div_cancel hp0.ne'] at this
  have hmod : (i + 1) % o = (i + 0) % o := by
    rw [add_zero, ← hg _ hr1 i hi, ← hg _ h1 (i + 1) hi1, hconst]
  have h10 : 1 ≡ 0 [MOD o] := Nat.ModEq.add_left_cancel' i hmod
  exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.card_H2_eq_same_action : ∀ {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M] (rho : Representation R G M) (rho' : Representation S G M), (∀ g m, rho g m = rho' g m) → Nat.card (H2 rho) = Nat.card (H2 rho') := by
  first | exact @GlobalTheory.H2CardScalars.card_H2_eq_of_same_action | exact GlobalTheory.H2CardScalars.card_H2_eq_of_same_action | (intros; apply GlobalTheory.H2CardScalars.card_H2_eq_of_same_action <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory

theorem norm_eTwoPi_I_mul (y : ℝ) : ‖eTwoPi (Complex.I * y)‖ = Real.exp (-(2 * Real.pi * y)) := by
  rw [eTwoPi, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem laurent_coeff_neg_eq_zero_of_bounded : ∀ (F : ℂ⸨X⸩) (T C : ℝ),
    (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) →
    ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  intro F T C h m hm
  by_contra hne
  have hF : F ≠ 0 := by rintro rfl; exact hne (by simp)
  have hm₀le : F.order ≤ m := by
    by_contra hlt; push_neg at hlt; exact hne (HahnSeries.coeff_eq_zero_of_lt_order hlt)
  have hc : F.coeff F.order ≠ 0 := fun h0 => hF (HahnSeries.coeff_order_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (le_of_lt (lt_of_le_of_lt hm₀le hm))
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  set m₀ := F.order with hm₀
  set y₁ : ℝ := max T 0 + 1 with hy₁
  have hy₁T : T < y₁ := by have := le_max_left T 0; linarith
  have hy₁0 : 0 < y₁ := by have := le_max_right T 0; linarith
  obtain ⟨x₁, hx₁, -⟩ := h (Complex.I * y₁) (by simpa using hy₁T)
  set q₁ := eTwoPi (Complex.I * y₁) with hq₁
  set ρ₁ := ‖q₁‖ with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁, hq₁, norm_eTwoPi_I_mul]; exact Real.exp_pos _
  have hS : Summable (fun m : ℤ => ‖F.coeff m * q₁ ^ m‖) := hx₁.summable.norm
  set S := ∑' m : ℤ, ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k with hSdef
  have key : ∀ y : ℝ, y₁ ≤ y →
      ‖F.coeff m₀‖ ≤ C * Real.exp (-(2 * Real.pi * y)) ^ k + Real.exp (-(2 * Real.pi * y)) / ρ₁ * S := by
    intro y hy
    obtain ⟨x, hx, hxC⟩ := h (Complex.I * y) (by simpa using lt_of_lt_of_le hy₁T hy)
    set q := eTwoPi (Complex.I * y) with hq
    set ρ := ‖q‖ with hρ
    have hρe : ρ = Real.exp (-(2 * Real.pi * y)) := norm_eTwoPi_I_mul y
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρe, hρ₁, hq₁, norm_eTwoPi_I_mul, Real.exp_le_exp]
      nlinarith [Real.pi_pos]
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    set r : ℤ → ℂ := fun m => F.coeff m * q ^ m * q ^ k - (if m = m₀ then F.coeff m₀ else 0) with hr
    have h2 : HasSum r (x * q ^ k - F.coeff m₀) := (hx.mul_right (q ^ k)).sub (hasSum_ite_eq m₀ _)
    have hbd : ∀ m, ‖r m‖ ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by
      intro m
      have hRnn : 0 ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by positivity
      by_cases hmm : m = m₀
      · subst hmm
        have : q ^ m₀ * q ^ k = 1 := by
          rw [hk, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq0)]
        have : r m₀ = 0 := by simp only [hr, mul_assoc, this, mul_one]; simp
        rw [this, norm_zero]; exact hRnn
      rcases lt_or_gt_of_ne hmm with hlt | hgt
      · have : r m = 0 := by simp only [hr, if_neg hmm, HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul, sub_zero]
        rw [this, norm_zero]; exact hRnn
      · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ m - m₀ - 1 by omega)
        have hm : m = (n + 1 : ℕ) - (k : ℤ) := by push_cast; omega
        have e1 : ∀ t : ℝ, t ≠ 0 → t ^ m * t ^ k = t ^ (n + 1) := fun t ht => by
          rw [← zpow_natCast t k, ← zpow_add₀ ht, ← zpow_natCast]; congr 1; omega
        have hρpos : 0 < ρ := by rw [hρe]; exact Real.exp_pos _
        have hrm : ‖r m‖ = ‖F.coeff m‖ * (ρ ^ m * ρ ^ k) := by
          simp only [hr, if_neg hmm, sub_zero, norm_mul, norm_pow, norm_zpow, ← hρ, mul_assoc]
        have hq₁m : ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k = ‖F.coeff m‖ * (ρ₁ ^ m * ρ₁ ^ k) := by
          rw [norm_mul, norm_zpow, ← hρ₁, mul_assoc]
        rw [hrm, hq₁m, e1 ρ hρpos.ne', e1 ρ₁ hρ₁pos.ne']
        have hpow : ρ ^ n ≤ ρ₁ ^ n := pow_le_pow_left₀ hρ0 hρle n
        have hc0 : 0 ≤ ‖F.coeff m‖ := norm_nonneg _
        rw [pow_succ, pow_succ]
        calc ‖F.coeff m‖ * (ρ ^ n * ρ) ≤ ‖F.coeff m‖ * (ρ₁ ^ n * ρ) := by gcongr
          _ = ρ / ρ₁ * (‖F.coeff m‖ * (ρ₁ ^ n * ρ₁)) := by field_simp
    have hg : HasSum (fun m => ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k)) (ρ / ρ₁ * S) :=
      (hS.mul_right (ρ₁ ^ k)).hasSum.mul_left _
    have h3 : ‖x * q ^ k - F.coeff m₀‖ ≤ ρ / ρ₁ * S := by
      rw [← h2.tsum_eq]; exact tsum_of_norm_bounded hg hbd
    have h4 : ‖x * q ^ k‖ ≤ C * ρ ^ k := by
      rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_right hxC (by positivity)
    rw [← hρe]
    calc ‖F.coeff m₀‖ = ‖x * q ^ k - (x * q ^ k - F.coeff m₀)‖ := by ring_nf
      _ ≤ ‖x * q ^ k‖ + ‖x * q ^ k - F.coeff m₀‖ := norm_sub_le _ _
      _ ≤ C * ρ ^ k + ρ / ρ₁ * S := add_le_add h4 h3
  have hlim : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
      (Filter.tendsto_id.const_mul_atTop (by positivity)))
  have hlim2 : Filter.Tendsto (fun y : ℝ => C * Real.exp (-(2 * Real.pi * y)) ^ k +
      Real.exp (-(2 * Real.pi * y)) / ρ₁ * S) Filter.atTop (nhds 0) := by
    have := ((hlim.pow k).const_mul C).add ((hlim.div_const ρ₁).mul_const S)
    simpa [zero_pow hk0] using this
  have hle : ‖F.coeff m₀‖ ≤ 0 :=
    ge_of_tendsto hlim2 (Filter.eventually_atTop.2 ⟨y₁, key⟩)
  exact hc (norm_le_zero_iff.1 hle)

end GlobalTheory
end
