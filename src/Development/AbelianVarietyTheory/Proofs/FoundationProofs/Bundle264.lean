module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle258
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM

def rkPsi (k : ℕ) (s : ℝ) (h b : ℕ → ℂ) (τ : ℍ) : ℂ :=
  conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)

theorem rankin_transf (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ)
    (h b : ℕ → ℂ) (s : ℝ) (hNL : N ∣ L) (hh : CF (2 * e + 1) L (ch ε) h) (hb : MF e L χ b)
    (hχ : ∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    rkPsi (2 * e + 1) s h b (γ • τ) =
      φ ((γ 1 1 : ℤ) : ZMod L) * trm (e + 1) s (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * rkPsi (2 * e + 1) s h b τ := by
  set j : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hjdef
  have hdenom : UpperHalfPlane.denom γ τ = j := ModularGroup.denom_apply γ τ
  have hj : j ≠ 0 := by rw [← hdenom]; exact UpperHalfPlane.denom_ne_zero _ τ
  have him : (γ • τ).im = τ.im / Complex.normSq j := by rw [ModularGroup.im_smul_eq_div_normSq, hdenom]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨m, hm⟩ := hγ
  have hcop : IsCoprime (γ 1 1) (L : ℤ) := ⟨γ 0 0, -(γ 0 1 * m), by rw [hm] at hdet; linear_combination hdet⟩
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    obtain ⟨n, hn⟩ := hNL
    have h1 : ((γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) : ℤ) : ZMod N) = 1 := by
      rw [hm, hn] at hdet; push_cast at hdet
      have : γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) = 1 := by linear_combination hdet
      rw [this]; simp
    push_cast at h1; simp only [mul_neg, neg_mul, ZMod.natCast_self, mul_zero, neg_zero, add_zero] at h1
    exact ⟨⟨_, ((γ 0 0 : ℤ) : ZMod N), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hεε : conj (ch ε (γ 1 1)) * ch ε (γ 1 1) = 1 := by
    have hn : ‖ch ε (γ 1 1)‖ = 1 := by
      unfold ch; rw [← hunit.unit_spec]; exact DirichletCharacter.unit_norm_eq_one ε hunit.unit
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hH := hh.1.2 γ ⟨m, hm⟩ τ
  have hB := hb.2 γ ⟨m, hm⟩ τ
  rw [hχ _ hcop] at hB
  rw [← hjdef] at hH hB
  have hNpos : 0 < Complex.normSq j := Complex.normSq_pos.2 hj
  have hy := τ.im_pos
  unfold rkPsi trm
  rw [hH, hB, him, Real.div_rpow hy.le hNpos.le, Real.rpow_add hNpos, Real.rpow_natCast]
  have hn2 : ‖j‖ ^ (-2 * s) = (Complex.normSq j ^ s)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    congr 1; push_cast; ring
  rw [hn2]
  have hP : (Complex.normSq j ^ s) ≠ 0 := (Real.rpow_pos_of_pos hNpos s).ne'
  have hcj : conj j ≠ 0 := by simpa using hj
  have hNc : ((Complex.normSq j : ℝ) : ℂ) = j * conj j := (Complex.mul_conj j).symm
  simp only [ch] at hεε ⊢
  have hε0 : ε ((γ 1 1 : ℤ) : ZMod N) ≠ 0 := by intro h0; rw [h0, mul_zero] at hεε; exact zero_ne_one hεε
  have hεc : conj (ε ((γ 1 1 : ℤ) : ZMod N)) = (ε ((γ 1 1 : ℤ) : ZMod N))⁻¹ := eq_inv_of_mul_eq_one_left hεε
  push_cast
  rw [hNc]
  simp only [map_mul, map_pow, hεc]
  field_simp
  ring_nf

theorem latF_kills (L : ℕ) (φ : DirichletCharacter ℂ L) (hφ : φ ≠ 1) :
    Kills L (0, 1) (latF L (fun _ => 1) φ) := by
  intro x
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have h0 : ∑ z : ZMod (n + 1), φ z = 0 := MulChar.sum_eq_zero_of_ne_one hφ
  unfold latF
  have e1 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).1 = x.1 := by intro r; simp
  by_cases hx : ((n + 1 : ℕ) : ℤ) ∣ x.1
  · have e2 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).2 = x.2 - r := by intro r; simp
    simp only [e1, e2, hx, if_true, one_mul]
    rw [← h0]
    refine Finset.sum_nbij' (fun r : ℕ => (((x.2 - r : ℤ)) : ZMod (n + 1)))
      (fun z => ((x.2 : ZMod (n + 1)) - z).val) (fun _ _ => Finset.mem_univ _)
      (fun z _ => Finset.mem_range.2 (ZMod.val_lt _)) ?_ ?_ (fun _ _ => rfl)
    · intro r hr
      have hr' : r < n + 1 := Finset.mem_range.1 hr
      simp [ZMod.val_cast_of_lt hr']
    · intro z _
      simp
  · simp only [e1, hx, if_false, Finset.sum_const_zero]

theorem rankin_summ (e : ℕ) (h b : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (hs : 0 < s)
    (hb : ∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1))
    (hh : Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s)) :
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) ∧
      LSeriesSummable (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := hb
  have hb2 : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((GlobalTheory.T.summable_card_divisors_sq_div_one_add_rpow s hs).mul_left (C ^ 2))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : (2 * (e : ℝ) - 1 + s) ≠ 0 := by
        have : (1 : ℝ) ≤ e := by exact_mod_cast he
        linarith
      simp [Real.zero_rpow this]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have key : (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) = ((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hn0]
      congr 1; push_cast [Nat.cast_sub he]; ring
    have hA : 0 < (n : ℝ) ^ (e - 1) := by positivity
    have hB : 0 < (n : ℝ) ^ (1 + s) := Real.rpow_pos_of_pos hn0 _
    have hle := hC n hn.ne'
    rw [key, div_le_iff₀ (by positivity)]
    calc ‖b n‖ ^ 2 ≤ (C * n.divisors.card * (n : ℝ) ^ (e - 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C ^ 2 * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + s)) * (((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s)) := by
        field_simp
  refine ⟨hb2, ?_⟩
  unfold LSeriesSummable
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((hh.add hb2).div_const 2))
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [Complex.ofReal_re, norm_mul, Complex.norm_conj]
  have e1 : (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n * n := by
    rw [← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']; congr 1; push_cast; ring
  have e2 : (n : ℝ) ^ (2 * (e : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n := by
    rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
  rw [e1, e2]
  have hu : 0 < (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := Real.rpow_pos_of_pos hn0 _
  set u := (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)
  set A := ‖h n‖
  set B := ‖b n‖
  have : (A ^ 2 / (u * n * n) + B ^ 2 / u) / 2 - A * B / (u * n) = (A - B * n) ^ 2 / (2 * u * n ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ (A - B * n) ^ 2 / (2 * u * n ^ 2) := by positivity
  linarith

theorem rankin_unfold : ∀ (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → 0 < L → N ∣ L → Wt L ρ → φ ≠ 1 → CF (2 * e + 1) L (ch ε) h → MF e L χ b → (∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) → (∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1)) → pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) = LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) * (((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
  intro e L N ε φ χ ρ h b s he hs hL hNL hρ hφ hh hb hχ hbC
  have hcont := fun a (ha : PolyB a) => (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).2
  set Lφ := LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) with hLφ
  have hlat : ∀ τ : ℍ, lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ = Lφ *
      ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm (e + 1) s ((x.1.1 : ℂ) * τ + x.1.2) := by
    intro τ
    have hb1 : ∃ C : ℝ, ∀ x, ‖latF L (fun _ => 1) φ x‖ ≤ C := ⟨1, fun x => by
      unfold latF; split_ifs <;> simp [DirichletCharacter.norm_le_one]⟩
    rw [(GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills (e + 1) L s (0, 1) _ τ (by omega) hs hL hb1 (latF_kills L φ hφ)).2]
    exact GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out (e + 1) L s φ τ (by omega) hs hL
  set Ψ := rkPsi (2 * e + 1) s h b with hΨ
  set W : ℤ × ℤ → ℍ → ℂ := fun x τ => φ (x.2 : ZMod L) * trm (e + 1) s ((x.1 : ℂ) * τ + x.2) * Ψ τ with hW
  have hpt : ∀ τ : ℍ, (ρ τ : ℂ) * (conj (qs h τ) * (qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) * (τ.im : ℂ) ^ (2 * e + 1)) =
      Lφ * ((ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ) := by
    intro τ
    rw [hlat τ]
    simp only [hW]
    rw [tsum_mul_right]
    have hy : ((τ.im ^ (((2 * e + 1 : ℕ) : ℝ) + s) : ℝ) : ℂ) = (τ.im : ℂ) ^ (2 * e + 1) * ((τ.im ^ s : ℝ) : ℂ) := by
      rw [Real.rpow_add τ.im_pos, Real.rpow_natCast]; push_cast; ring
    simp only [hΨ, rkPsi, hy]
    ring
  have hmsq := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) L (ch ε) h (by omega) hh
  obtain ⟨hbsq, hLS⟩ := rankin_summ e h b s he hs hbC (by simpa using hmsq.2.2.1 s hs)
  have hint : IntegrableOn Ψ strip := by
    exact GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand (2 * e + 1) e L N ε h b s rfl he hs hL hNL hh hb.1 hbsq
  have hmeas : AEStronglyMeasurable Ψ := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hΨ, rkPsi]
    refine ((Complex.continuous_conj.comp (hcont h hh.1.1)).mul (hcont b hb.1)).mul (Complex.continuous_ofReal.comp ?_)
    exact (UpperHalfPlane.continuous_im).rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hunf := GlobalTheory.T.integral_coprime_sum_unfold_to_unitStrip L ρ Ψ W hρ hint hmeas (fun γ hγ τ => by
    simpa [hW] using rankin_transf e L N ε φ χ h b s hNL hh hb hχ γ hγ τ)
  have hmel := GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries h b (2 * (e : ℝ) + s) (by positivity) hh.1.1 hb.1 hmsq.1 hLS
  have hΨeq : (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((2 * (e : ℝ) + s) + 1) : ℝ) : ℂ)) = Ψ := by
    funext τ; simp only [hΨ, rkPsi]; congr 3; push_cast; ring
  rw [hΨeq] at hmel
  unfold pet
  simp_rw [hpt]
  rw [integral_const_mul, hunf, hmel hint]

end GlobalTheory.EisM
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertParity.FiniteOrder

theorem exists_prime_mem {R : Type*} [CommRing R] (P : Ideal R) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : R) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ (q : R) ∈ P := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | (apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem ..)

theorem simple_case (D : D7) (S : Type) [AddCommGroup S] [Module (𝓞 D.host.E) S] [Finite S]
    [IsSimpleModule (𝓞 D.host.E) S] :
    Ev D (Nat.card S) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card S → InertQ D q) → sgn D (Nat.card S) = -1) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := 𝓞 D.host.E) (M := S)).1 ‹_›
  have hc : Nat.card S = Ideal.absNorm P := by
    rw [Nat.card_congr e.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Ideal.absNorm P ≠ 0 := hc ▸ Nat.card_pos.ne'
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP
  rw [hc]
  refine ⟨h1, fun h => ?_⟩
  by_cases hs : D.host.conj • P = P
  · exact (h2 hs).1
  · obtain ⟨q, hq, hd, hm⟩ := exists_prime_mem P hP.isPrime _ h0 (Ideal.absNorm_mem P)
    exact absurd (h q hq hd) ((h3 hs).2 q hq hm)

theorem card_parity_sign_length_of_eq (D : D7) (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M],
    Nat.card M = n → Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) →
      sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ hn
    rcases subsingleton_or_nontrivial M with hM | hM
    · have h1 : Nat.card M = 1 := Nat.card_of_subsingleton (0 : M)
      rw [h1, Module.length_eq_zero]
      exact ⟨Ev.one, fun _ => by simp [sgn_one]⟩
    · obtain ⟨N, hN⟩ : ∃ N : Submodule (𝓞 D.host.E) M, IsCoatom N := by
        rcases eq_top_or_exists_le_coatom (⊥ : Submodule (𝓞 D.host.E) M) with h | ⟨N, hN, -⟩
        · exact absurd h bot_ne_top
        · exact ⟨N, hN⟩
      haveI : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
      haveI : IsSimpleModule (𝓞 D.host.E) (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
      haveI : Nontrivial (M ⧸ N) := IsSimpleModule.nontrivial (𝓞 D.host.E) (M ⧸ N)
      have hc : Nat.card M = Nat.card N * Nat.card (M ⧸ N) := Submodule.card_eq_card_quotient_mul_card N
      have hq : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
      have hp : 0 < Nat.card N := Nat.card_pos
      obtain ⟨a1, a2⟩ := ih (Nat.card N) (by rw [← hn, hc]; exact lt_mul_of_one_lt_right hp hq) N rfl
      obtain ⟨b1, b2⟩ := simple_case D (M ⧸ N)
      have hl : Module.length (𝓞 D.host.E) M =
          Module.length (𝓞 D.host.E) N + Module.length (𝓞 D.host.E) (M ⧸ N) :=
        Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
          (LinearMap.exact_subtype_mkQ N)
      have hfin : Module.length (𝓞 D.host.E) N ≠ ⊤ := Module.length_ne_top
      rw [hl, Module.length_eq_one (R := 𝓞 D.host.E) (M := M ⧸ N), ENat.toNat_add hfin (by simp), hc]
      refine ⟨a1.mul b1 hp.ne' (by omega), fun h => ?_⟩
      rw [sgn_mul a1 b1 hp.ne' (by omega), a2 fun q hq hd => h q hq (hd.mul_right _),
        b2 fun q hq hd => h q hq (hd.mul_left _), pow_add]
      simp

theorem ev_card_and_sgn_card : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M], Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) → sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) :=
  fun D M _ _ _ => card_parity_sign_length_of_eq D _ M rfl

end GlobalTheory.InertParity.FiniteOrder
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.DatumBasic

variable {p : ℕ} [Fact p.Prime]

theorem wModel_Δ (lam : Qbar →+* ℂ_[p]) {Λ : AddSubgroup ℂ} (h2 : g2 Λ ∈ Qbar) (h3 : g3 Λ ∈ Qbar)
    (hd : TaylorLogMetric.discr Λ = 1) : (wModel lam Λ).Δ = 1 := by
  set a : Qbar := ⟨g2 Λ, h2⟩ with ha
  set b : Qbar := ⟨g3 Λ, h3⟩ with hb
  have hc : ∀ x : Qbar, lamC lam (-(x : ℂ) / 4) = -(lam x) / 4 := by
    intro x
    have e : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast
      rfl
    rw [e, lamC, dite_eq_left (-x / 4).2]
    change lam (-x / 4) = _
    rw [map_div₀, map_neg, map_ofNat]
  have e : a ^ 3 - 27 * b ^ 2 = 1 := by
    apply Subtype.ext
    push_cast
    exact hd
  have e2 := congrArg lam e
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one] at e2
  have ea := hc a
  have eb := hc b
  simp only [ha, hb] at ea eb
  simp only [wModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ea, eb]
  linear_combination e2

theorem intSer_of_isWq {W : WeierstrassCurve ℂ_[p]} (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) {w : PowerSeries ℂ_[p]}
    (h : IsWq W w) : IntSer w := by
  obtain ⟨hr, -, hC, hX, -⟩ := SerRing.series_ring_laws p
  have hadd : ∀ {f g : PowerSeries ℂ_[p]}, IntSer f → IntSer g → IntSer (f + g) :=
    fun hf hg => (hr _ _ hf hg).1
  have hterm : ∀ (c : ℂ_[p]) (i j : ℕ) (t : PowerSeries ℂ_[p]), ‖c‖ ≤ 1 → IntSer t →
      IntSer (PowerSeries.C c * PowerSeries.X ^ i * t ^ j) := fun c i j t hc ht =>
    SerRing.intSer_mul (SerRing.intSer_mul ((hC c).2 hc) (SerRing.intSer_pow hX i))
      (SerRing.intSer_pow ht j)
  have hone : IntSer (1 : PowerSeries ℂ_[p]) := by simpa using SerRing.intSer_pow hX 0
  have key : ∀ n : ℕ, ∃ t : PowerSeries ℂ_[p], IntSer t ∧ PowerSeries.X ^ n ∣ w - t := by
    intro n
    induction n with
    | zero => exact ⟨1, hone, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, z, hz⟩ := ih
      refine ⟨_, hadd (hadd (hadd (hadd (hadd hone (hterm _ 1 1 t h1 ht)) (hterm _ 2 1 t h2 ht))
        (hterm _ 3 2 t h3 ht)) (hterm _ 4 2 t h4 ht)) (hterm _ 6 3 t h6 ht),
        z * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2)), ?_⟩
      have h' : w = 1 + PowerSeries.C W.a₁ * PowerSeries.X * w +
          PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C W.a₃ * PowerSeries.X ^ 3 * w ^ 2 +
          PowerSeries.C W.a₄ * PowerSeries.X ^ 4 * w ^ 2 +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 6 * w ^ 3 := h
      linear_combination h' + (PowerSeries.X * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2))) * hz
  intro n
  obtain ⟨t, ht, hd⟩ := key (n + 1)
  have e := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at e
  rw [e]
  exact ht n

theorem datum_basic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → ‖((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ IntSer g.wq⁻¹ ∧ PowerSeries.constantCoeff g.wq⁻¹ = 1 ∧ PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  intro p _ g ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hw, _⟩ hL a2 a3 hd
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have := congrArg PowerSeries.constantCoeff hw
    simpa using this
  refine ⟨?_, SerRing.intSer_inv (intSer_of_isWq h1 h2 h3 h4 h6 hw) (by rw [hw0, norm_one]),
    by rw [PowerSeries.constantCoeff_inv, hw0, inv_one],
    GlobalTheory.ThetaParam.constantCoeff_ePhi1 g hw (GlobalTheory.OddTheta.sgStar_laws _ hL).1.2.1,
    GlobalTheory.ThetaParam.atU_sg g ((hL.sg_eq_zero 0).2 (zero_mem _))⟩
  rw [WeierstrassCurve.variableChange_Δ, wModel_Δ g.lam a2 a3 hd, mul_one, norm_pow] at hΔ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hΔ

end GlobalTheory.EvenTheta.DatumBasic
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Filter Topology

theorem U1_sgStar_pow_eight : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ →
    U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  intro Λ hΛ t ht h2t
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have laws := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hd : Differentiable ℂ (sgStar Λ) := laws.1.1
  have hd0 : deriv (sgStar Λ) 0 = 1 := laws.1.2.1
  have hz0 : sgStar Λ 0 = 0 := (laws.2.1 0).2 Λ.zero_mem
  have hzw : sgStar Λ (2 * t) = 0 := (laws.2.1 _).2 h2t
  have htL : t ∉ L.lattice := fun h => ht ((hL t).2 h)
  have hD0 : L.derivWeierstrassP t = 0 :=
    (GlobalTheory.derivWeierstrassP_eq_zero_iff L htL).2 (by rw [← two_mul]; exact (hL _).1 h2t)

  have hA : HasDerivAt (fun z => sgStar Λ (2 * z)) (deriv (sgStar Λ) (2 * t) * 2) t := by
    have := (hd (2 * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul (2 : ℂ))
    rw [mul_one] at this
    exact this
  have hB : HasDerivAt (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4)
      (-(6 * L.weierstrassP t ^ 2 - L.g₂ / 2) * sgStar Λ t ^ 4 +
        -(L.derivWeierstrassP t) * ((4 : ℕ) * sgStar Λ t ^ (4 - 1) * deriv (sgStar Λ) t)) t :=
    (GlobalTheory.hasDerivAt_derivWeierstrassP L htL).neg.mul ((hd t).hasDerivAt.pow 4)
  have hev : (fun z => sgStar Λ (2 * z)) =ᶠ[𝓝 t] (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds htL] with z hz
    have hz' : z ∉ Λ := fun h => hz ((hL z).1 h)
    rw [GlobalTheory.SigmaDuplication.sgStar_two_mul hΛ hz', GlobalTheory.LatticeInvariants.wpD_eq hL z]
  have hu := hA.unique (hB.congr_of_eventuallyEq hev)
  rw [hD0] at hu

  set s : ℂ := if 2 * t / 2 ∈ Λ then 1 else -1 with hs
  have hfun : U1 Λ (2 * t) (sgStar Λ) = fun z => s * sgStar Λ z := funext (hΛ.sg_law h2t)
  have hE : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) := by fun_prop
  have hC : HasDerivAt (U1 Λ (2 * t) (sgStar Λ))
      (deriv (sgStar Λ) (0 + 2 * t) * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) +
        sgStar Λ (0 + 2 * t) * deriv (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) 0) 0 :=
    ((hd _).hasDerivAt.comp_add_const 0 (2 * t)).mul (hE 0).hasDerivAt
  have hC' : HasDerivAt (U1 Λ (2 * t) (sgStar Λ)) (s * 1) 0 := by
    rw [hfun, ← hd0]; exact (hd 0).hasDerivAt.const_mul s
  have hv := hC.unique hC'
  rw [zero_add, hzw] at hv
  have hs2 : s ^ 2 = 1 := by rw [hs]; split_ifs <;> norm_num
  have hU : U1 Λ t (sgStar Λ) 0 = sgStar Λ t * Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) := by
    simp only [U1, zero_add]
    congr 1
    congr 1
    ring
  have hexp : Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) =
      Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4 := by
    rw [← Complex.exp_nat_mul, map_mul, map_ofNat]
    congr 1
    push_cast
    ring
  rw [hexp] at hv
  have key : U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) = -2 * s := by
    rw [hU, mul_pow]
    linear_combination (Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4) * hu - 2 * hv

  have hcub : 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
    have := L.derivWeierstrassP_sq t htL
    rw [hD0] at this
    linear_combination -this
  obtain ⟨hg2, hg3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  rw [hg2, hg3, (hw t ht).1]
  linear_combination (1 / 4 : ℂ) * (U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) - 2 * s) * key
    + hs2 - 2 * L.weierstrassP t * U1 Λ t (sgStar Λ) 0 ^ 8 * hcub

end GlobalTheory.HalfPeriodValue
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicComplex_integral_bounded_series_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  first | exact @GlobalTheory.EvenTheta.SerRing.series_ring_laws | exact GlobalTheory.EvenTheta.SerRing.series_ring_laws | (intros; apply GlobalTheory.EvenTheta.SerRing.series_ring_laws <;> assumption)
end
