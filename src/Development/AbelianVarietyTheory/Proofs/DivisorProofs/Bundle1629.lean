module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.NumberTheory.Harmonic.Bounds
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeightTieProof

theorem formHeight_eq_ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) :
    formHeight δ w A f = ht w A f + (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2 := by
  have hr : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold ht formHeight
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
  field_simp
  ring

theorem ht_pow (hM : HtMul) {F : Type} [Field F] [NumberField F] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hL : Lat w A Λ) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) (e : ℕ) :
    ht w A (f ^ e) = e * ht w A f := by
  induction e with
  | zero =>
    have := (hM F B N n w A Λ hL).2 1 one_ne_zero
    simpa using this
  | succ k ih =>
    have hk : IsMultiHomogeneous (k • a) (f ^ k) :=
      isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 ha).pow k)
    rw [pow_succ, (hM F B N n w A Λ hL).1 (k • a) a _ _ (pow_ne_zero k hf) hf hk ha, ih]
    push_cast; ring

theorem heightTie : HtMul → HeightTie := by
  intro hM F _ _ T Λ hL h hh d e f c hf he hc
  obtain ⟨d', f', -, hf', e'⟩ := hh
  obtain ⟨rfl, c', hc', rfl⟩ := hf.isChowFormInt.unique hf'.isChowFormInt
  have hf0 := hf.isChowFormInt.ne_zero
  have hd := hf.isChowFormInt.pos
  rw [HeightUnique.formHeight_C_mul hL.pos d hL.spans hL.det hf0 hf.homog hc', formHeight_eq_ht] at e'
  have hpow : IsMultiHomogeneous (e • fun _ => d) (f ^ e) :=
    isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 hf.homog).pow e)
  have key : ht T.w T.A (C c * f ^ e) = e * ht T.w T.A f := by
    unfold ht
    rw [HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det (pow_ne_zero e hf0) hpow hc]
    exact ht_pow hM hL hf0 hf.homog e
  have hD : (0 : ℝ) < (T.D : ℝ) + 1 := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have eq1 : ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) =
      h - (harmonic (T.N - 1) : ℝ) / 2 := by
    rw [key, div_eq_iff (by push_cast; positivity)]
    push_cast
    push_cast at e'
    have : ht T.w T.A f = ((T.D : ℝ) + 1) * d * h - ((T.D : ℝ) + 1) * d * (harmonic (T.N - 1) : ℝ) / 2 := by
      linarith
    rw [this]; ring
  refine ⟨eq1, ?_⟩
  rw [eq1]

  have hNn : T.N ≤ T.n := by
    have h1 := finrank_range_le_card (R := F) (b := T.w.col)
    rw [Set.finrank, hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hH : (harmonic (T.N - 1) : ℝ) ≤ 1 + Real.log (T.N - 1 : ℕ) := harmonic_le_one_add_log _
  have hlog : Real.log (T.N - 1 : ℕ) ≤ Real.log T.n := by
    rcases Nat.eq_zero_or_pos (T.N - 1) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : T.N - 1 ≤ T.n))
  linarith

end GlobalTheory.HeightTieProof
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShortNum

theorem claimS_to_hsClaimS : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ →
    h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  intro T D n Λ β Λ₀ ΛD ΛT δ h h' d deg hD hT hn hΛ hβ hδ hh hC
  obtain ⟨hz0, hz1, hineq⟩ := hC
  unfold Formalism.NormVectorIdentities.Items.HSClaimS Formalism.NormVectorIdentities.Items.hsZ Formalism.NormVectorIdentities.Items.hsR Formalism.NormVectorIdentities.Items.hsLogRho Formalism.NormVectorIdentities.Items.hsG
  set z : ℝ := 1 - ((T - 1).choose D : ℝ) * δ / d with hz
  refine ⟨hz0, hz1, ?_⟩
  set ρ : ℝ := Real.log Λ + 26 * Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) with hρ
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hT2 : (2 : ℝ) ≤ T := by
    have : 2 ≤ T := by omega
    exact_mod_cast this
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hβpos : 0 < β := by linarith
  have h1 : Real.log (Real.exp ρ * T) = ρ + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' hTpos.ne', Real.log_exp]
  have h2 : Real.log (2 * Real.exp ρ * Real.sqrt β) = Real.log 2 + ρ + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr hβpos).ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt hβpos.le]
  have hX : (2 : ℝ) ≤ 2 + |h| + Real.log Λ := by have := abs_nonneg h; linarith
  have hprod : 2 * n ≤ n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ) := by
    have a1 : n ≤ n * (D : ℝ) := by nlinarith
    have a2 : n ≤ n * (D : ℝ) * 1 * δ := by nlinarith
    nlinarith
  have hlog2n : Real.log 2 + Real.log n ≤ Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hprod
  have hl2 := Real.log_two_gt_d9
  have hcst : HSShort.cst n Λ = Real.log n + Real.log Λ + (Real.log n + 1) / 2 := by
    unfold HSShort.cst; rw [Real.log_mul (by linarith) (by linarith)]
  have hc : HSShort.cst n Λ ≤ ρ := by rw [hcst, hρ]; linarith
  have hc0 : 0 ≤ HSShort.cst n Λ := by rw [hcst]; positivity
  rw [h1, h2]
  clear h1 h2 hprod hlog2n hcst hX
  generalize HSShort.cst n Λ = c at *
  clear_value ρ z
  generalize (T : ℝ) = t at *
  generalize (D : ℝ) = e at *
  generalize Real.log t = lt at *
  generalize Real.log n = ln at *
  generalize Real.log β = lb at *
  have hA : t * h - 3 * (e + 1) * |h| - Real.log Λ₀ - 26 * e ^ 2 * (ρ + lt)
        - (t + e + 1) * lb - (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2)
      ≤ t * h' - e * (e + 1) * c - Real.log Λ₀ - t / 2 * lb := by
    have e1 : t * h - t * ((ln + 1) / 2) ≤ t * h' := by
      have := mul_le_mul_of_nonneg_left hh hTpos.le
      linarith
    have e2 : e * (e + 1) * c ≤ 26 * e ^ 2 * (ρ + lt) := by
      have : e * (e + 1) ≤ 2 * e ^ 2 := by nlinarith
      have hD2 : 0 ≤ e ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_right this hc0, mul_nonneg hD2 hlogT, mul_le_mul_of_nonneg_left hc hD2,
        mul_nonneg hD2 hc0]
    have e3 : t / 2 * lb ≤ (t + e + 1) * lb := mul_le_mul_of_nonneg_right (by linarith) hlogβ
    have e4 : t * ((ln + 1) / 2) ≤ (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2) := by
      have hg : (ln + 1) / 2 ≤ (e + 1) * (ln + 1) / 2 + 1 + 2 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e) (by linarith : (0 : ℝ) ≤ ln + 1)]
      have hT' : t ≤ t + e ^ 2 := by linarith [sq_nonneg e]
      calc t * ((ln + 1) / 2) ≤ t * ((e + 1) * (ln + 1) / 2 + 1 + 2) :=
            mul_le_mul_of_nonneg_left hg hTpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hT' (by positivity)
    have e5 : 0 ≤ 3 * (e + 1) * |h| := by positivity
    linarith
  have hB : t * c + t / 2 * lb + Real.log ΛD + Real.log ΛT
      ≤ t * (Real.log 2 + ρ + lb / 2) + Real.log ΛD + Real.log ΛT := by
    have : t * c ≤ t * (Real.log 2 + ρ) := mul_le_mul_of_nonneg_left (by linarith) hTpos.le
    linarith
  have hz1' : 0 ≤ 1 - z := by linarith
  have m1 := mul_le_mul_of_nonneg_left hA hz1'
  have m2 := mul_le_mul_of_nonneg_left hB hz0
  linarith

end GlobalTheory.HSShortNum
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.CoeffInt

theorem word_col {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (g : Fin t → Fin n) :
    word mul (fun i => w.col (g i)) =
      ∑ e : Fin t → Fin N, (∏ i, w (e i) (g i)) • word mul (fun i => Pi.single (e i) 1) := by
  let Φ := (MultilinearMap.mkPiAlgebraFin K t (Module.End K A)).compLinearMap (fun _ => mul)
  have hΦ : ∀ u : Fin t → Fin N → K, word mul u = Φ u := by
    intro u; simp [Φ, word, MultilinearMap.mkPiAlgebraFin_apply]
  have hcol : ∀ i, w.col (g i) = ∑ j, w j (g i) • (Pi.single j 1 : Fin N → K) := by
    intro i; funext k; simp [Matrix.col, Finset.sum_apply, Pi.single_apply]
  rw [hΦ]
  simp_rw [hcol]

  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MultilinearMap.map_smul_univ, hΦ]
  rfl

theorem linSubst_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (c : A →ₗ[K] K)
    (β : Fin t → Fin B) (x : A) :
    linSubst w (coordP mul c β x) =
      ∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K) := by
  rw [show (∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) =
      ∑ g : Fin t → Fin n, ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) x)) *
        ((∏ i, C (w (e i) (g i))) * ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) from ?_]
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [linSubst, coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, algebraMap_eq]
    simp_rw [Fintype.prod_sum, Finset.mul_sum, ← Finset.prod_mul_distrib]
    exact Finset.sum_comm
  · refine Finset.sum_congr rfl fun g _ => ?_

    rw [word_col, LinearMap.sum_apply, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, ← map_prod, map_mul]
    ring

theorem prod_X_monomial {σ K : Type} [Field K] {t : ℕ} (f : Fin t → σ) :
    ∃ s, (∏ i, (X (f i) : MvPolynomial σ K)) = monomial s 1 := by
  refine Finset.prod_induction _ (fun q => ∃ s, q = monomial s 1) ?_ ?_ ?_
  · rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩; exact ⟨s + s', by rw [monomial_mul, one_mul]⟩
  · exact ⟨0, by simp⟩
  · intro i _; exact ⟨_, rfl⟩

end GlobalTheory.HSShort.CoeffInt


open GlobalTheory.HSShort.CoeffInt in
theorem GlobalTheory.HSShort.colCoeff_mem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m • b i ∈ S.M S.T := by
  intro F A _ _ _ _ _ _ S hS d b c hco κ hx m
  obtain ⟨-, hM⟩ := GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS κ.j κ.t (le_of_eq κ.add)
  have tr : ∀ j', j' = S.T → ∀ y' ∈ S.M j', ∃ y ∈ S.M S.T, (y : A) = (y' : A) := by
    rintro j' rfl y' hy'; exact ⟨y', hy', rfl⟩
  have key : ∀ g : Fin κ.t → Fin S.n, ∃ y ∈ S.M S.T,
      (y : A) = word S.mul (fun i => S.w.col (g i)) (κ.x : A) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := hM g κ.x hx
    obtain ⟨z, hz, hzeq⟩ := tr _ κ.add y hy
    exact ⟨z, hz, hzeq.trans hyeq⟩
  choose Y hY hYeq using key
  have hex : ∀ g : Fin κ.t → Fin S.n, ∃ s,
      (∏ i, (X (κ.β i, g i) : MvPolynomial (Fin _ × Fin S.n) F)) = monomial s 1 := by
    intro g
    exact GlobalTheory.HSShort.CoeffInt.prod_X_monomial (K := F) (fun i => (κ.β i, g i))
  choose s hs using hex
  have hcoef : ∀ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m =
      ∑ g, b.repr (Y g) i * (if s g = m then 1 else 0) := by
    intro i
    rw [GlobalTheory.HSShort.CoeffInt.linSubst_coordP, coeff_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_C_mul, hs g, coeff_monomial, ← hYeq g, hco]
  simp_rw [hcoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun g _ => ?_
  have hsum : ∑ i, (b.repr (Y g) i * (if s g = m then (1 : F) else 0)) • b i =
      (if s g = m then (1 : F) else 0) • Y g := by
    conv_rhs => rw [← b.sum_repr (Y g), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hsum]
  split_ifs
  · rw [one_smul]; exact hY g
  · rw [zero_smul]; exact zero_mem _
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DeepStep

theorem ofFn_prod_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) :
    ∀ (n : ℕ) (g : Fin n → M) (k : Fin n → ℕ), (∀ i, p (g i) (k i)) → p (List.ofFn g).prod (∑ i, k i) := by
  intro n
  induction n with
  | zero => intro g k _; simpa using h1
  | succ n ih =>
    intro g k hg
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact hmul _ _ _ _ (hg 0) (ih _ _ fun i => hg i.succ)

theorem pow_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) (a : M) (ha : p a 1) : ∀ n, p (a ^ n) n := by
  intro n
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hmul _ _ _ _ ih ha

section Inter

variable {F E A A' : Type} [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A']
  (ι : A →ₛₗ[algebraMap F E] A')

theorem ofFn_prod_comm : ∀ (n : ℕ) (g' : Fin n → Module.End E A') (g : Fin n → Module.End F A),
    (∀ i x, g' i (ι x) = ι (g i x)) → ∀ x, (List.ofFn g').prod (ι x) = ι ((List.ofFn g).prod x) := by
  intro n
  induction n with
  | zero => intro g' g _ x; simp
  | succ n ih =>
    intro g' g hg x
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, mul_apply_eq_comp, mul_apply_eq_comp,
      ih _ _ (fun i => hg i.succ), hg 0]

theorem pow_comm (f' : Module.End E A') (f : Module.End F A) (h : ∀ x, f' (ι x) = ι (f x)) :
    ∀ (n : ℕ) x, (f' ^ n) (ι x) = ι ((f ^ n) x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih => intro x; rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, h, ih]

theorem mem_span_image (Y : Set A) : ∀ y ∈ Submodule.span F Y, ι y ∈ Submodule.span E (ι '' Y) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end Inter

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

def Up (S : Sys F A) (f : Module.End F A) (k : ℕ) : Prop := ∀ j, j + k ≤ S.T → ∀ x ∈ S.V j, f x ∈ S.V (j + k)

theorem up_one (S : Sys F A) : Up S 1 0 := fun j _ x hx => by simpa using hx

theorem up_mul (S : Sys F A) : ∀ a b k l, Up S a k → Up S b l → Up S (a * b) (k + l) := by
  intro a b k l ha hb j hj x hx
  have h1 := hb j (by omega) x hx
  have h2 := ha (j + l) (by omega) _ h1
  rw [mul_apply_eq_comp]
  have e : j + (k + l) = j + l + k := by omega
  rw [e]; exact h2

theorem up_mul_gen (S : Sys F A) (hS : S.Hyp) (u : Fin S.N → F) : Up S (S.mul u) 1 := by
  intro j hj x hx
  have := (GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS j 1 hj).1 (fun _ => u) x hx
  simpa [word] using this

theorem up_pw (S : Sys F A) (hS : S.Hyp) (s : Fin S.D → Fin S.N → F) (α : Fin S.D →₀ ℕ) :
    Up S (pw S.mul s α) α.degree := by
  rw [Finsupp.degree_eq_sum]
  exact ofFn_prod_induct (Up S) (up_one S) (up_mul S) S.D _ _
    fun i => pow_induct (Up S) (up_one S) (up_mul S) _ (up_mul_gen S hS (s i)) (α i)

end GlobalTheory.HSShort.DeepStep


open GlobalTheory.HSShort.DeepStep in
theorem GlobalTheory.HSShort.deepStep_finrank : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ), FiniteDimensional E (Φ.U (S.T - S.D)) ∧ Module.finrank E (Φ.U (S.T - S.D)) = S.deepRank s ∧ S.deepRank s ≤ Module.finrank F (S.V S.T) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ
  set P : Submodule F A := ⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (S.V S.D).map (pw S.mul s α.1) with hP
  have hle := hS.le_T
  have hPT : P ≤ S.V S.T := iSup_le fun α => by
    rintro _ ⟨x, hx, rfl⟩
    have h := up_pw S hS s α.1 S.D (by rw [α.2]; omega) x hx
    have e : S.D + α.1.degree = S.T := by rw [α.2]; omega
    rw [e] at h
    exact h
  haveI : FiniteDimensional F (S.V S.T) := by
    obtain ⟨r, b, -⟩ := hS.shortT
    exact Module.Finite.of_basis b
  haveI : FiniteDimensional F P := Submodule.finiteDimensional_of_le hPT
  have hdeep : S.deepRank s = Module.finrank F P := rfl
  let b := Module.finBasis F P
  let v : Fin (Module.finrank F P) → A := fun i => (b i : A)
  have hv : Submodule.span F (Set.range v) = P := by
    have : Set.range v = (P.subtype) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent E (fun i => Φ.ι (v i)) := by
    refine Φ.indep _ (fun i => (⟨v i, hPT (b i).2⟩ : S.V S.T)) ?_
    refine LinearIndependent.of_comp (S.V S.T).subtype ?_
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hcomm : ∀ (α : Fin S.D →₀ ℕ) (x : A),
      pw Φ.mul (fun i k => algebraMap F E (s i k)) α (Φ.ι x) = Φ.ι (pw S.mul s α x) := fun α x =>
    ofFn_prod_comm Φ.ι _ _ _ (fun i y => pow_comm Φ.ι _ _ (fun z => Φ.mul_ι (s i) z) (α i) y) x
  have hU : Φ.U (S.T - S.D) = Submodule.span E (Set.range fun i => Φ.ι (v i)) := by
    rw [Φ.div]
    apply le_antisymm
    · refine iSup_le fun α => ?_
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, hcomm]
      have h1 : pw S.mul s α.1 x ∈ P := Submodule.mem_iSup_of_mem α ⟨x, hx, rfl⟩
      rw [← hv] at h1
      have h2 := mem_span_image Φ.ι _ _ h1
      rwa [← Set.range_comp] at h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hvi : v i ∈ P := (b i).2
      exact Submodule.iSup_induction (fun α : MonoDeg (Fin S.D) (S.T - S.D) => (S.V S.D).map (pw S.mul s α.1))
        (motive := fun y => Φ.ι y ∈ ⨆ α : MonoDeg (Fin S.D) (S.T - S.D),
          (Submodule.span E (Φ.ι '' S.V S.D)).map (pw Φ.mul (fun i k => algebraMap F E (s i k)) α.1)) hvi
        (fun α y hy => by
          obtain ⟨x, hx, rfl⟩ := hy
          rw [← hcomm]
          exact Submodule.mem_iSup_of_mem α (Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩)))
        (by simp only [map_zero]; exact zero_mem _)
        (fun y z hy hz => by simp only [map_add (f := _)]; exact add_mem hy hz)
  refine ⟨?_, ?_, ?_⟩
  · rw [hU]; exact FiniteDimensional.span_of_finite E (Set.finite_range _)
  · rw [hU, finrank_span_eq_card hli, Fintype.card_fin, hdeep]
  · rw [hdeep]; exact Submodule.finrank_mono hPT
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.hermitianMultiplicationFlat_columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  first | exact @GlobalTheory.HSShort.ColEval.columns_eval | exact GlobalTheory.HSShort.ColEval.columns_eval | (intros; apply GlobalTheory.HSShort.ColEval.columns_eval <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.CentCls
end
