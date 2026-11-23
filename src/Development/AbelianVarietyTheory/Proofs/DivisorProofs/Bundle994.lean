module

public import Formalism.LocalRingCardinality.Bundle007
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle115
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle831
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeLoss

open IsDedekindDomain

theorem additiveValuation_mul_of_ne_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

theorem additiveValuation_conj_place_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneIdeal_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conj (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneIdeal_iff_additiveValuation_pos _ y hy, mem_heightOneIdeal_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conj_place_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

theorem logWeight_conj (D : D7) (w : D.what₂.places.Pl) :
    SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w := by
  unfold SizeData₂.lwP
  rw [plEq_conj]
  exact Formalism.DivisionValues.ValuationRepresentative.lw_conjPl (D.plEq w)

theorem additiveValuation_residueChar_eq_ramIndex (D : D7) (w : D.what₂.places.Pl) :
    vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
  have h0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have h1 := D.val_eq w _ h0
  rw [D.what₂.places.val_resChar] at h1
  exact_mod_cast h1.symm

theorem exists_over (D : D7) (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset D.what₂.places.Pl, ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p := by
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  refine ⟨(T.map D.plEq.symm.toEmbedding).filter (fun w => D.what₂.places.resChar w = p), fun w => ?_⟩
  rw [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_symm, hT]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ resChar_mem D w, h⟩⟩

theorem sum_half (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p) (y : D.what₂.LL) (hy : y * star y = (p : D.what₂.LL)) :
    ∑ w ∈ S, 2 * SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) = Real.log p := by
  have hp0 : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  have hconj : ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) =
      ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) := by
    refine Finset.sum_nbij' D.what₂.places.conj D.what₂.places.conj ?_ ?_ ?_ ?_ ?_
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      rw [logWeight_conj, additiveValuation_conj_place_eq_star]
  have hm := factEtaMean D p hp S hS
  rw [← hm]
  have : ∀ w ∈ S, lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ) =
      SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) + SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) := by
    intro w hw
    have h1 := additiveValuation_residueChar_eq_ramIndex D w
    rw [(hS w).1 hw, ← hy, additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)] at h1
    have h2 : (D.what₂.places.ramIdx w : ℝ) = (vAdd (D.plEq w) y : ℝ) + (vAdd (D.plEq w) (star y) : ℝ) := by
      exact_mod_cast h1.symm
    rw [h2, ← mul_add]
    rfl
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hconj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem conj_sigmaOf {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) :
    H.conj (H.sigmaOf g x) = H.sigmaOf g (H.conj x) := by
  have h1 : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj :=
    map_mul (H.gal).symm g (R.cc)
  have h2 : H.sigmaOf (R.cc * g) = H.conj * H.sigmaOf g :=
    map_mul (H.gal).symm (R.cc) g
  have h3 : H.conj * H.sigmaOf g = H.sigmaOf g * H.conj := by rw [← h1, ← h2, mul_comm]
  exact congrArg (fun s : H.E ≃ₐ[ℚ] H.E => s x) h3

theorem tauPib_norm {D : D7} (X : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    tauPib X i τ * star (tauPib X i τ) = (D.host.g i : D.what₂.LL) := by
  unfold tauPib tauLL
  rw [← D.embE_conj, conj_sigmaOf, ← map_mul, ← map_mul, ← map_mul, X.piG_norm]
  simp

theorem padic_log_le (p n : ℕ) (hp : p.Prime) : (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.padicValNat_def]
  · have h : p ^ padicValNat p n ≤ n := Nat.le_of_dvd hn (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    rw [← Real.log_pow]
    apply Real.log_le_log
    · have := hp.pos
      positivity
    · exact_mod_cast h

theorem arith_bound (δ v e lg f m b L N η C₁ C₂ cg CY B : ℝ) (hB : B = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hL : 1 ≤ L) (hN : 1 ≤ N) (hCY : 0 ≤ CY) (hδ : |δ| ≤ C₁ * f * b) (hv0 : 0 ≤ v)
    (hv : v ≤ C₂ * f * N * Real.log (f * N)) (he : e = cg * f * (N ^ 2 + m ^ 2 * η)) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ (CY + 1) * L) (hη0 : 0 ≤ η) (hNη : N ^ 2 ≤ η) (hmf : m ≤ f) (hfη : f * η ≤ b) :
    |δ * lg + 2 * v + 2 * e * lg| ≤ (|C₁| * (CY + 1) + 2 * |C₂| + 4 * |cg| * (CY + 1)) * B := by
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hηb : η ≤ b := le_trans (le_mul_of_one_le_left hη0 hf) hfη
  have hb : 0 ≤ b := hη0.trans hηb
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have hB1 : f * b * L ≤ B := by
    have : B = m * (f * b * L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (mul_nonneg hfb hL0) hm
  have hB2 : f * b ≤ B := le_trans (le_mul_of_one_le_right hfb hL) hB1
  have t1 : |δ * lg| ≤ |C₁| * (CY + 1) * B := by
    rw [abs_mul, abs_of_nonneg hlg0]
    have h1 : |δ| ≤ |C₁| * (f * b) := by
      refine hδ.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hfb
    calc |δ| * lg ≤ |C₁| * (f * b) * ((CY + 1) * L) := mul_le_mul h1 hlg hlg0 (by positivity)
      _ = |C₁| * (CY + 1) * (f * b * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : v ≤ |C₂| * B := by
    have hfN : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf hN
    have l0 : 0 ≤ Real.log (f * N) := Real.log_nonneg hfN
    have l1 : Real.log (f * N) ≤ f * N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h1 : f * N * Real.log (f * N) ≤ B := by
      calc f * N * Real.log (f * N) ≤ f * N * (f * N) := mul_le_mul_of_nonneg_left l1 (by linarith)
        _ = f * (f * N ^ 2) := by ring
        _ ≤ f * b := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hNη hf0).trans hfη) hf0
        _ ≤ B := hB2
    calc v ≤ C₂ * (f * N * Real.log (f * N)) := by rw [← mul_assoc, ← mul_assoc]; exact hv
      _ ≤ |C₂| * (f * N * Real.log (f * N)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (by linarith) l0)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have t3 : |2 * e * lg| ≤ 4 * |cg| * (CY + 1) * B := by
    have h0 : 0 ≤ N ^ 2 + m ^ 2 * η := by positivity
    have h1 : N ^ 2 + m ^ 2 * η ≤ 2 * (m * b) := by
      have a1 : m * η ≤ b := (mul_le_mul_of_nonneg_right hmf hη0).trans hfη
      have a2 : m * (m * η) ≤ m * b := mul_le_mul_of_nonneg_left a1 hm0
      have a3 : b ≤ m * b := le_mul_of_one_le_left hb hm
      nlinarith
    have h2 : |2 * e * lg| = 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) := by
      rw [he, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlg0, abs_of_nonneg h0, abs_of_nonneg hf0]
      simp only [abs_two]
      ring
    rw [h2]
    calc 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) ≤ 2 * |cg| * f * (2 * (m * b) * ((CY + 1) * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hlg hlg0 (by positivity)) (by positivity)
      _ = _ := by rw [hB]; ring
  have tri : |δ * lg + 2 * v + 2 * e * lg| ≤ |δ * lg| + |2 * v| + |2 * e * lg| := abs_add_three _ _ _
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * v)] at tri
  nlinarith

end GlobalTheory.TypeLoss

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.ConjOverQuad

theorem under_eq_or_smul_under_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (b : L)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v : Ideal (𝓞 L)) [v.IsPrime] (hv : ((p : ℕ) : 𝓞 L) ∈ v)
    (Q : Ideal (𝓞 (IntermediateField.adjoin ℚ {b}))) [Q.IsPrime]
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ∨
      (c⁻¹ • v).under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 L)))
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    rw [hWQ.over, Ideal.mem_under] at hQ
    simpa using hQ
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hv
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hpW
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v W (L ≃ₐ[ℚ] L)
  rcases hb σ with h1 | h1
  · left
    rw [hWQ.over, ← hσ, GlobalTheory.Mem.Chr.under_smul_of_fix b σ h1]
  · right
    have h2 : (σ * c) b = b := by
      rw [AlgEquiv.mul_apply, hc, map_neg, h1, neg_neg]
    have h4 : (σ * c) • c⁻¹ • v = W := by rw [mul_smul, smul_inv_smul, hσ]
    rw [hWQ.over, ← h4, GlobalTheory.Mem.Chr.under_smul_of_fix b _ h2]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem div_or_conj_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E)), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → P.Div k w ∨ ∃ w' : HeightOneSpectrum (𝓞 D.host.E), P.Div k w' ∧ w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal := by
  intro D P k w hw
  have hG : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hsq := D.host.sqrtMinusD_sq
  have hc := D.host.conj_sqrtMinusD
  have hb : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      σ D.host.sqrtMinusD = D.host.sqrtMinusD ∨ σ D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  have := w.isPrime
  have hQ := (P.pb k).isPrime
  rcases @under_eq_or_smul_under_eq _ _ _ _ _ (D.host.g_prime k) D.host.sqrtMinusD hb D.host.conj hc w.asIdeal _ hw
    (P.pb k).asIdeal hQ (P.pb_over k) with h | h
  · exact Or.inl (HeightOneSpectrum.ext h)
  · refine Or.inr ⟨Formalism.L2.Col.conjPrime₂ w, HeightOneSpectrum.ext ?_, (Formalism.L2.Col.conjIdeal_asIdeal w).symm⟩
    have e : (Formalism.L2.Col.conjPrime₂ w).asIdeal = D.host.conj⁻¹ • w.asIdeal := by
      ext y
      rw [Formalism.L2.Col.mem_conjP, Ideal.mem_inv_pointwise_smul_iff]
      have : Formalism.L2.Col.cO D.host.E y = D.host.conj • y :=
        RingOfIntegers.ext (bridge_star_holds D.R D.host (y : D.host.E))
      rw [this]
    show ((Formalism.L2.Col.conjPrime₂ w).asIdeal).under (𝓞 D.host.K) = _
    rw [e]
    exact h

end GlobalTheory.ConjOverQuad
end

section

noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.Col

namespace GlobalTheory.HeckeParts

section Grp

variable {G : Type} [Group G] {J Q L : Subgroup G}

def Splits (Q J L : Subgroup G) : Prop :=
  ∀ κ ∈ Q, ∃ k₁ ∈ J, ∃ k₂, k₁ ∈ L ∧ κ = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

def RInv (J : Subgroup G) (F : G → ℂ) : Prop := ∀ k ∈ J, ∀ h, F (h * k) = F h

theorem Splits.self (h : Splits Q J L) (hJ : J ≤ Q) :
    ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l := by
  intro k hk
  obtain ⟨k₁, h₁, k₂, hL, e, hc⟩ := h k (hJ hk)
  refine ⟨k₁, h₁, k₂, ?_, hL, e, hc⟩
  have : k₂ = k₁⁻¹ * k := by rw [e]; group
  rw [this]
  exact J.mul_mem (J.inv_mem h₁) hk

theorem RInv.one {F : G → ℂ} (h : RInv J F) (k : J) (g : G) : F (g * k) = (((1 : J →* ℂˣ) k : ℂˣ) : ℂ) • F g := by
  simp [h k k.2 g]

theorem isDC_of_splits (hs : Splits Q J L) (hJ : J ≤ Q) {x : G} (hx : x ∈ L) {A : Finset G} (hA : ∀ a ∈ A, a ∈ L)
    {K : Set G} (hK : ∀ g, g ∈ K ↔ g ∈ J ∧ g ∈ L) (h1 : ∀ γ ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * x * k₂)
    (h2 : ∀ y, (∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * x * k₂) → ∃! γ, γ ∈ A ∧ γ⁻¹ * y ∈ K) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h1 a ha
    exact ⟨⟨k₁, ((hK _).1 h₁).1⟩, ⟨k₂, ((hK _).1 h₂).1⟩, e⟩
  · rintro g ⟨k, k', rfl⟩
    obtain ⟨k₁, h₁, k₂, h₂, hL, e, hc⟩ := hs.self hJ k k.2
    have key : ∀ a : G, a⁻¹ * ((k : G) * x * k') = a⁻¹ * (k₁ * x * 1) * (k₂ * k') := by
      intro a
      rw [e, mul_assoc k₁ k₂ x, (hc x hx).eq]; group
    have hm : k₂ * (k' : G) ∈ J := J.mul_mem h₂ k'.2
    refine (existsUnique_congr fun a => and_congr_right fun ha => ?_).1
      (h2 _ ⟨k₁, (hK _).2 ⟨h₁, hL⟩, 1, (hK _).2 ⟨J.one_mem, L.one_mem⟩, rfl⟩)
    rw [key, J.mul_mem_cancel_right hm, hK]
    exact and_iff_left (L.mul_mem (L.inv_mem (hA a ha)) (L.mul_mem (L.mul_mem hL hx) L.one_mem))

theorem dcOp_eq_rInv {x x' : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) {F : G → ℂ} (hF : RInv J F) :
    dcOp A F = dcOp A' F ∧ RInv J (dcOp A F) := by
  have := GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx hF.one
  exact ⟨this.1, fun k hk h => by simpa using this.2 ⟨k, hk⟩ h⟩

theorem dcOp_rInv {x : G} {A : Finset G} (hA : IsDC J x A) {F : G → ℂ} (hF : RInv J F) : RInv J (dcOp A F) :=
  (dcOp_eq_rInv hA hA ⟨1, 1, by simp⟩ hF).2

theorem dcOp_translate (hs : Splits Q J L) {x : G} {A : Finset G} (hA : IsDC J x A) (hL : ∀ a ∈ A, a ∈ L)
    {F : G → ℂ} (hF : RInv J F) {κ : G} (hκ : κ ∈ Q) (h : G) :
    dcOp A F (h * κ) = dcOp A (fun g => F (g * κ)) h := by
  obtain ⟨k₁, h₁, k₂, hl, rfl, hc⟩ := hs κ hκ
  rw [← (hc k₁ hl).eq, ← mul_assoc, dcOp_rInv hA hF k₁ h₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  show F (h * k₂ * a) = F (h * a * (k₂ * k₁))
  rw [← mul_assoc, hF k₁ h₁, mul_assoc, (hc a (hL a ha)).eq, mul_assoc]

theorem dcOp_comm_of_commute {A B : Finset G} (h : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (F : G → ℂ) :
    dcOp A (dcOp B F) = dcOp B (dcOp A F) := by
  funext g
  simp only [dcOp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  rw [mul_assoc, (h a ha b hb).eq, mul_assoc]

end Grp

section Normal

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end Normal

end GlobalTheory.HeckeParts

end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.CMSize

theorem mulStable_one_add {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 + w) := by
  intro x hx
  rw [add_mul, one_mul]
  exact add_mem hx (h x hx)

theorem mulStable_one_sub {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 - w) := by
  intro x hx
  rw [sub_mul, one_mul]
  exact sub_mem hx (h x hx)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  intro l hl lam d L Ω P M hd hd4 hw hΩ hM hP hMP
  have hlp : l.Prime := hl.out
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero _))
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hs0 : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.pos
    exact (Real.sqrt_pos.mpr this).ne'
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hwdef
  have hre : w.re = 0 := by simp [hwdef]
  have him : w.im = Real.sqrt d := by simp [hwdef]
  have him0 : w.im ≠ 0 := by rw [him]; exact hs0
  have hw2 : w ^ 2 = -(d : ℂ) := by
    have h1 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
      rw [← Complex.ofReal_mul, hs]; simp
    rw [hwdef, mul_pow, Complex.I_sq, sq, h1]; ring
  have hn0 : Complex.normSq w = (d : ℕ) := by
    rw [Complex.normSq_apply, hre, him, hs]; simp
  have hn1 : Complex.normSq (1 + w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hn2 : Complex.normSq (1 - w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  have hp : Sz l lam 0 (12 * (L.weierstrassP P / Ω ^ 2)) := by
    refine hsz (M ^ 2) _ (fun h => hM (hlp.dvd_of_dvd_pow h)) ?_
    have := ((GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L w Ω M hw him0 hΩ hM0).1 P hMP).1
    convert this using 1
    push_cast; ring
  have key : ∀ (α : ℂ) (n : ℕ), MulStable L α → Complex.normSq α = n → ¬ l ∣ n →
      Sz l lam 0 ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) -
        (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)) := by
    intro α n hα hn hln
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hln (dvd_zero _))
    refine hsz ((M * n) ^ 2) _ (fun h => ?_) ?_
    · rcases (Nat.Prime.dvd_mul hlp).1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hM h
      · exact hln h
    · have := GlobalTheory.T.isogeny_formula_weierstrassP_integral L α w Ω P M n hw him0 hΩ hα hn hn0 hM0 hP hMP
      rwa [Nat.cast_pow]
  by_cases hld : l = d
  · subst hld
    rw [if_neg (by omega), if_pos rfl]
    have hnd : ¬ l ∣ 1 + l := by
      intro h
      have : l ∣ 1 := (Nat.dvd_add_left (dvd_refl l)).1 h
      exact hlp.one_lt.ne' (Nat.dvd_one.1 this)
    have h1 := key (1 + w) (1 + l) (mulStable_one_add hw) hn1 hnd
    refine GlobalTheory.T.algebraicValuation_bound_at_ramified_prime l lam w _ _ hd4 hw2 hp ?_
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  · rw [if_neg hld]
    by_cases h3 : l = 3 ∧ d % 3 = 1
    · obtain ⟨rfl, h3⟩ := h3
      rw [if_neg (by omega)]
      have hnd : ¬ 3 ∣ 1 + d := by omega
      have h1 := key (1 + w) (1 + d) (mulStable_one_add hw) hn1 hnd
      have h2 := key (1 - w) (1 + d) (mulStable_one_sub hw) hn2 hnd
      refine GlobalTheory.T.valuation_bound_three_inert lam d w _ (L.weierstrassP P / Ω ^ 2) h3 hw2 ?_ ?_
      · simpa only [Nat.cast_add, Nat.cast_one] using h1
      · simpa only [Nat.cast_add, Nat.cast_one] using h2
    · have hnd : ¬ l ∣ d := fun h => hld ((Nat.prime_dvd_prime_iff_eq hlp hd).1 h)
      have h1 := key w d hw hn0 hnd
      refine GlobalTheory.T.valuation_bound_multiplier_sqrt_neg_d l lam d _ _ hd hd4 hld hp ?_ ?_
      · convert h1 using 1
        rw [hw2]; ring
      · rintro rfl
        have : ¬ d % 3 = 1 := fun h => h3 ⟨rfl, h⟩
        omega

end GlobalTheory.CMSize
end
