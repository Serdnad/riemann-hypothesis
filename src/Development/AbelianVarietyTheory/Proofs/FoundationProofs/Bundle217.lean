module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle058
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle118
public import Mathlib.FieldTheory.KrullTopology
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
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
import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.KummerExtension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.LSeries.Convergence
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem div_le_half_sq_add {t x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    t / x ≤ (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 := by
  have key : (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 - t / x = (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by
    field_simp
    ring
  have : 0 ≤ (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by positivity
  linarith

theorem lseriesSummable_of_sq (a : ℕ → ℂ) (k : ℕ)
    (hsq : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s))
    (s : ℂ) (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable a s := by
  set σ := s.re with hσ
  set δ : ℝ := σ - ((k : ℝ) + 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := hsq δ hδ0
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + δ)) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · have : 0 ≤ ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := by positivity
    have : 0 ≤ (n : ℝ) ^ (-(1 + δ)) := by positivity
    linarith
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have e : (n : ℝ) ^ (-(1 + δ)) = (n : ℝ) ^ ((k : ℝ) + δ) * ((n : ℝ) ^ σ)⁻¹ * ((n : ℝ) ^ σ)⁻¹ := by
      rw [show -(1 + δ) = ((k : ℝ) + δ) + -σ + -σ by rw [hδ]; ring, Real.rpow_add hn', Real.rpow_add hn',
        Real.rpow_neg hn'.le]
    rw [e]
    exact div_le_half_sq_add (Real.rpow_pos_of_pos hn' σ) (Real.rpow_pos_of_pos hn' _)

theorem lseries_cusp_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  intro k L N ε g hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε g hk hL hNL hcf
  have hcoef : ∀ n, (qExpansion 1 ⇑f).coeff n = g n := fun n => by
    have h := GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane g hcf.1.1 n
    rw [coef, ← hf] at h
    exact h
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hsq := (GlobalTheory.T.rankin_mean_square_cuspForm k L (ch ε) g hk hcf).2.2.1
  have hsum : ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s := lseriesSummable_of_sq g k hsq
  have habs : LSeries.abscissaOfAbsConv g ≤ (((((k : ℝ) + 1) / 2 : ℝ)) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hsum y (by simpa using hy)
  have hdiff : Differentiable ℂ (ModularForm.L hk0 f) := CuspForm.differentiable_L hk0 f

  have hagree : ∀ s : ℂ, (k : ℝ) / 2 + 1 < s.re → LSeries g s = ModularForm.L hk0 f s := by
    intro s hs
    have h := CuspForm.hasSum_L hk0 f (s := s) (by rw [Int.cast_natCast]; exact hs)
    simp only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    have hs0 : s ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hs; have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    rw [LSeries, ← h.tsum_eq]
    congr 1
    funext n
    rw [LSeries.term_of_ne_zero' hs0, hcoef]
  refine ⟨ModularForm.L hk0 f, hdiff, fun s hs => ⟨hsum s hs, ?_⟩⟩
  set U : Set ℂ := {c : ℂ | ((k : ℝ) + 1) / 2 < c.re} with hU
  have hLU : AnalyticOnNhd ℂ (LSeries g) U := (LSeries_analyticOnNhd g).mono fun c hc => by
    simp only [Set.mem_setOf_eq, hU] at hc ⊢
    exact lt_of_le_of_lt habs (by exact_mod_cast hc)
  have hΛU : AnalyticOnNhd ℂ (ModularForm.L hk0 f) U := fun z _ => hdiff.analyticAt z
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  set z₀ : ℂ := (((k : ℝ) + 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (k : ℝ) + 2 := by rw [hz₀, Complex.ofReal_re]
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hz₀U : z₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hz₀re]; linarith
  have hev : LSeries g =ᶠ[𝓝 z₀] ModularForm.L hk0 f := by
    have hopen : IsOpen {c : ℂ | (k : ℝ) / 2 + 1 < c.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp only [Set.mem_setOf_eq, hz₀re]; linarith)] with c hc
    exact hagree c hc
  exact hLU.eqOn_of_preconnected_of_eventuallyEq hΛU hconn hz₀U hev hs

end GlobalTheory.EisM
end
end

section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow_eq_one' (T : Tower p Ω) (m : ℕ) : T.ζ (m + 1) ^ p ^ m = T.ζ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, T.ζpow, ih]

theorem exists_pow_eq_zeta_one (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ e : ℕ, (T.ζ N ^ j) ^ e = T.ζ 1 := by
  have hN : N ≠ 0 := by rintro rfl; simp at hjN; omega
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hglt : Nat.gcd j (p ^ (M + 1)) < p ^ (M + 1) :=
    lt_of_le_of_lt (Nat.le_of_dvd hj0 (Nat.gcd_dvd_left _ _)) hjN
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hglt
  obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hp.out).1 (Nat.gcd_dvd_right j (p ^ (M + 1)))
  have haM : a ≤ M := by
    by_contra h
    have : a = M + 1 := by omega
    subst this
    have h2 : p ^ (M + 1) ∣ j := hga ▸ Nat.gcd_dvd_left _ _
    exact absurd (Nat.le_of_dvd hj0 h2) (by omega)
  obtain ⟨t, ht⟩ : Nat.gcd j (p ^ (M + 1)) ∣ p ^ M := hga ▸ pow_dvd_pow p haM
  refine ⟨m * t, ?_⟩
  rw [← pow_mul, ← zeta_pow_eq_one' T M, Basic.zeta_pow_eq_iff]
  have h1 : j * m ≡ Nat.gcd j (p ^ (M + 1)) [MOD p ^ (M + 1)] := by
    unfold Nat.ModEq; rw [hm, Nat.mod_eq_of_lt hglt]
  have h2 := h1.mul_right t
  rw [← ht] at h2
  rw [← mul_assoc]; exact h2

theorem isInt_zeta (T : Tower p Ω) (N : ℕ) : IsInt (p := p) (T.ζ N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [(T.prim N).pow_eq_one]; exact isIntegral_one

theorem ggeo_zeta (T : Tower p Ω) (N : ℕ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) : g (T.ζ N) = T.ζ N := by
  apply hg
  refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos N) 1, ?_⟩
  simp [(T.prim N).pow_eq_one]

end GlobalTheory.K5.Decomp

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isInt_qq (T : Tower p Ω) (N : ℕ) : IsInt (p := p) (T.qq N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [Basic.qq_pow]; exact isIntegral_algebraMap

theorem exists_mult (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ s : Ω, IsInt (p := p) s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧ s * (T.ζ N ^ j - 1) = T.ζ 1 - 1 := by
  obtain ⟨e, he⟩ := exists_pow_eq_zeta_one T N j hj0 hjN
  refine ⟨∑ i ∈ Finset.range e, (T.ζ N ^ j) ^ i, ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun i _ => ((isInt_zeta T N).pow j).pow i
  · intro g hg

    simp only [map_sum, map_pow, ggeo_zeta T N hg]
  · rw [geom_sum_mul, he]

end GlobalTheory.K5.Decomp


open GlobalTheory.K5.Decomp in
theorem GlobalTheory.K5.Decomp.decomp : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt (p := p) y → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧ IsInt (p := p) w ∧
    (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq N y hy hfix
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer p Ω hΩ T N y hfix
  have hci := GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion p Ω hΩ T N c hc hy
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hs : ∀ j, ∃ s : Ω, IsInt (p := p) s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧
      (0 < j → j < p ^ N → s * (T.ζ N ^ j - 1) = T.ζ 1 - 1) := by
    intro j
    by_cases h : 0 < j ∧ j < p ^ N
    · obtain ⟨s, h1, h2, h3⟩ := exists_mult T N j h.1 h.2
      exact ⟨s, h1, h2, fun _ _ => h3⟩
    · exact ⟨0, isIntegral_zero, fun g _ => map_zero g, fun a b => absurd ⟨a, b⟩ h⟩
  choose s hsi hsg hse using hs
  refine ⟨c 0, ∑ j ∈ Finset.range (p ^ N), s j * c j * T.qq N ^ j, hci 0 hpos, hc 0, ?_, ?_, ?_⟩
  · refine IsIntegral.sum _ fun j hj => ?_
    exact ((hsi j).mul (hci j (Finset.mem_range.1 hj))).mul ((isInt_qq T N).pow j)
  · intro g hg
    have hg1 := (Subgroup.mem_inf.1 hg).1
    have hg2 : g (T.qq N) = T.qq N := (Subgroup.mem_inf.1 hg).2

    simp only [map_sum, map_mul, map_pow, hsg _ g hg1, hc _ g hg1, hg2]
  · obtain ⟨M, hM⟩ : ∃ M, p ^ N = M + 1 := ⟨p ^ N - 1, by omega⟩
    have key : ∀ i < M, s (i + 1) * (T.ζ N ^ (i + 1) - 1) = T.ζ 1 - 1 := fun i hi =>
      hse (i + 1) (Nat.succ_pos i) (by omega)

    simp only [map_sum, map_mul, map_pow, hsg _ τ hτ, hc _ τ hτ, hτq N]
    rw [hM, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range M, s (i + 1) * c (i + 1) * (T.ζ N * T.qq N) ^ (i + 1) =
        s (i + 1) * c (i + 1) * T.qq N ^ (i + 1) + (T.ζ 1 - 1) * (c (i + 1) * T.qq N ^ (i + 1)) := by
      intro i hi
      rw [← key i (Finset.mem_range.1 hi)]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem small_traces_subgroup : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (H : Subgroup (Gal p Ω)), H ≤ ⨅ n, Gn T n →
    ∀ (S : Finset Ω) (j : ℕ), 1 ≤ j → ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧
      (∀ g ∈ E, g ∈ H) ∧ (∀ h ∈ H, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
      ∑ g ∈ E, g y = T.ζ j - 1 := by
  intro p _ Ω _ _ hp2 hclo T H hH S j hj
  classical
  obtain ⟨v, hvint, hvgal, -, hv1, hsep⟩ := GlobalTheory.T.exists_valuation_almostEtale_towerFixer p Ω hp2 hclo T
  obtain ⟨U, -, hUfin, hUS, hUsep⟩ := hsep S
  let K : Subgroup (Gal p Ω) := ⨅ n, Gn T n
  let H' : Subgroup ↥K := H.subgroupOf K
  let U' : Subgroup ↥H' := U.subgroupOf H'
  haveI : U'.FiniteIndex := inferInstance
  haveI : Finite (↥H' ⧸ U') := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (↥H' ⧸ U') := Fintype.ofFinite _
  have hU'sep : AlmostSep v U' := GlobalTheory.T.fixedFieldAlmostEtale_subgroupOf Ω v ↥K U H' hUsep
  have hsmul : ∀ (h : ↥H') (x : Ω), h • x = ((h : ↥K) : Gal p Ω) x := fun _ _ => rfl
  have hinv : ∀ (h : ↥H') (x : Ω), v (h • x) = v x := fun h x => by rw [hsmul]; exact hvgal _ x
  have hfixζ : ∀ h : ↥H', h • (T.ζ j - 1) = T.ζ j - 1 := by
    intro h
    have hm : ((h : ↥K) : Gal p Ω) ∈ Gn T j := (Subgroup.mem_iInf.mp (h : ↥K).2) j
    have h1 : ((h : ↥K) : Gal p Ω) (T.ζ j) = T.ζ j := ((Basic.mem_gn T j _).mp hm).1
    rw [hsmul, map_sub, map_one, h1]
  have hve : v (T.ζ j - 1) < 1 := (GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hv1 j hj).1
  obtain ⟨y₀, hy₀, hy₀le, htr⟩ := GlobalTheory.T.exists_integer_cosetRepresentativeTrace_eq_of_lt_one Ω v ↥H' hinv U' hU'sep (T.ζ j - 1) hfixζ hve
  have hS : ∀ s ∈ S, s ∈ Fix Ω U' := fun s hs g =>
    hUS s hs ⟨((g : ↥H') : ↥K), Subgroup.mem_subgroupOf.mp g.2⟩
  obtain ⟨y, D, E', hy, huniq, hsum⟩ := GlobalTheory.T.exists_reps_of_cosetRepresentativeTrace Ω ↥H' U' S hS y₀ hy₀
  let ι : ↥H' ↪ Gal p Ω := ⟨fun h => ((h : ↥K) : Gal p Ω), fun a b hab => Subtype.ext (Subtype.ext hab)⟩
  have hιH : ∀ h : ↥H', ι h ∈ H := fun h => Subgroup.mem_subgroupOf.mp h.2
  have hιs : ∀ (h : ↥H') (x : Ω), ι h x = h • x := fun _ _ => rfl
  have hy₀int : IsInt (p := p) y₀ := (hvint y₀).mp hy₀le
  refine ⟨y, E'.map ι, ?_, ?_, ?_, ?_⟩
  · rw [hy]
    exact IsIntegral.sum _ fun d _ => by rw [← hιs]; exact Basic.isInt_gal _ hy₀int
  · intro g hg
    obtain ⟨g', -, rfl⟩ := Finset.mem_map.mp hg
    exact hιH g'
  · intro h hh
    let h' : ↥H' := ⟨⟨h, hH hh⟩, Subgroup.mem_subgroupOf.mpr hh⟩
    obtain ⟨g', ⟨hg'E, hg'y, hg'S⟩, hg'u⟩ := huniq h'
    refine ⟨ι g', ⟨Finset.mem_map_of_mem ι hg'E, ?_, ?_⟩, ?_⟩
    · rw [hιs]; exact hg'y
    · intro s hs; rw [hιs]; exact hg'S s hs
    · rintro g ⟨hgE, hgy, hgS⟩
      obtain ⟨g'', hg''E, rfl⟩ := Finset.mem_map.mp hgE
      congr 1
      refine hg'u g'' ⟨hg''E, ?_, ?_⟩
      · rw [← hιs]; exact hgy
      · intro s hs; rw [← hιs]; exact hgS s hs
  · rw [Finset.sum_map]
    exact (Finset.sum_congr rfl fun g _ => hιs g y).trans (hsum.trans htr)

end GlobalTheory.K5
end

section

open GlobalTheory.K5 Polynomial IntermediateField

noncomputable section

namespace GlobalTheory.K5.TauGen

theorem not_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := GlobalTheory.T.q_not_pth_pow_in_closure_algebraic_padicInt

def geoF (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x})

theorem isOpen_setOf_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (x : Ω) (P : Ω → Prop) : IsOpen {σ : Ω ≃ₐ[F] Ω | P (σ x)} := by
  haveI : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  have hU : IsOpen (((F⟮x⟯).fixingSubgroup : Subgroup (Ω ≃ₐ[F] Ω)) : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hV : IsOpen ((fun τ : Ω ≃ₐ[F] Ω => σ⁻¹ * τ) ⁻¹' ((F⟮x⟯).fixingSubgroup : Set (Ω ≃ₐ[F] Ω))) :=
    hU.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hV.mem_nhds ?_) ?_
  · show σ⁻¹ * σ ∈ (F⟮x⟯).fixingSubgroup
    rw [inv_mul_cancel]; exact one_mem _
  · intro τ hτ
    have h1 := (mem_fixingSubgroup_iff _ _).1 hτ x (mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have : σ⁻¹ (τ x) = x := h1
      calc τ x = σ (σ⁻¹ (τ x)) := by simp
        _ = σ x := by rw [this]
    show P (τ x)
    rw [h2]; exact hσ

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ T : Tower p Ω, ∃ τ ∈ Ggeo (p := p) Ω, ∀ n, τ (T.qq n) = T.ζ n * T.qq n := by
  intro p hp hp2 Ω _ _ hΩ T
  haveI := hΩ.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo hΩ
  have hO : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ geoF p Ω := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hA : ∀ x : Ω, IsAlgZp (p := p) x → x ∈ geoF p Ω := fun x hx => Subfield.subset_closure (Or.inr hx)
  let F := geoF p Ω
  let φ : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  have hφ : Function.Injective φ := fun a b h => hΩ.inj (congrArg Subtype.val h)
  have hcomp : (algebraMap F Ω).comp φ = algebraMap (O0 p) Ω := by ext a; rfl
  haveI hal : Algebra.IsAlgebraic F Ω := by
    constructor
    intro x
    obtain ⟨P, hP, hx⟩ := hΩ.alg.isAlgebraic x
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP, ?_⟩
    rw [aeval_def, eval₂_map, hcomp, ← aeval_def, hx]
  haveI : IsAlgClosure F Ω := ⟨inferInstance, hal⟩
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (Ω ≃ₐ[F] Ω) := inferInstance
  let q' : F := ⟨algebraMap (O0 p) Ω (qO p), hO _⟩
  have hirr : ∀ n, Irreducible (X ^ (p ^ n) - C q') := fun n =>
    irreducible_X_pow_sub_C_of_prime_pow_of_ne_two hp.out hp2 n (fun b hb =>
      not_pow p Ω hΩ (b : Ω) b.2 (by rw [← SubmonoidClass.coe_pow, hb]))
  have hmin : ∀ n (y : Ω), y ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) → minpoly F y = X ^ (p ^ n) - C q' := by
    intro n y hy
    refine (minpoly.eq_of_irreducible_of_monic (hirr n) ?_ (monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero))).symm
    simp only [map_sub, map_pow, aeval_X, aeval_C, hy]
    exact sub_self _
  let S : ℕ → Set (Ω ≃ₐ[F] Ω) := fun n => {σ | σ (T.qq n) = T.ζ n * T.qq n}
  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have h1 := hmin n (T.qq n) (Basic.qq_pow T n)
    have h2 := hmin n (T.ζ n * T.qq n) (by rw [mul_pow, (T.prim n).pow_eq_one, one_mul, Basic.qq_pow T n])
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) Ω).1 (h2.trans h1.symm)
    exact ⟨σ, hσ⟩
  have hdec : ∀ n, S (n + 1) ⊆ S n := by
    intro n σ hσ
    show σ (T.qq n) = T.ζ n * T.qq n
    have hσ' : σ (T.qq (n + 1)) = T.ζ (n + 1) * T.qq (n + 1) := hσ
    rw [← T.qpow n, map_pow, hσ', mul_pow, T.ζpow, T.qpow]
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    rw [← isOpen_compl_iff]
    exact isOpen_setOf_apply (F := F) (T.qq n) (fun y => ¬ y = T.ζ n * T.qq n)
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  let τ : Gal p Ω :=
    { σ.toRingEquiv with
      commutes' := fun a => σ.commutes (⟨algebraMap (O0 p) Ω a, hO a⟩ : F) }
  refine ⟨τ, fun x hx => σ.commutes (⟨x, hA x hx⟩ : F), fun n => hσ n⟩

end GlobalTheory.K5.TauGen
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ.StabHecke

theorem congruenceCondition_conj_diamond : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r →
    PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  intro N l d σ r hσ hr
  obtain ⟨h1, h2, -, h4⟩ := diam_facts hσ
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 =
      r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (r 0 0) * h4
  have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      σ 1 0 * (σ 1 1 * r 0 0 - σ 1 0 * r 0 1 - σ 1 1 * r 1 1) + σ 1 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, show r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 - 1 =
        (r 0 0 - 1) + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 by ring]
    exact dvd_add (dvd_add r1 (dvd_mul_of_dvd_left h1 _)) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right r3 _)
  · rw [e00]
    obtain ⟨s, hs⟩ := h2
    obtain ⟨t, ht⟩ := r3
    have e : r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 =
        r 0 0 + (l : ℤ) * (s * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * t) := by
      rw [hs, ht]; ring
    rw [e]
    exact r4.add_mul_left_left _

end GlobalTheory.KZ.StabHecke
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem blockOrd_finSumFinEquiv (p q : ℕ) :
    GlobalTheory.RealPar.BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have : a < b := hab
    exact (Fin.strictMono_castAdd q) this
  · exact hab.elim
  · exact hab.elim
  · have : a < b := hab
    exact (Fin.strictMono_natAdd p) this

end GlobalTheory.HolDS
end
