module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle098
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelMassDegreeTypeLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle122
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open GlobalTheory.Col PowerSeries

theorem GlobalTheory.Col.normOp_frob : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  intro R _ p _ σ hfl h
  obtain ⟨b, -⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hfl.complete
  exact GlobalTheory.Col.NormFrob.normOp_eq_smap_add p σ hfl b h
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.EmbInj

theorem emb_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
      Function.Injective ι := by
  intro p _ Ω _ _ hc T n hn ι _
  obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite _ _
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker (ι : On p n →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap (O0 p) Ω a = 0 := by
      rw [← ι.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hc.inj (this.trans (map_zero _).symm)
  intro x hx
  have : x ∈ RingHom.ker (ι : On p n →+* Ω) := hx
  rwa [hker, Ideal.mem_bot] at this

end GlobalTheory.K5.EmbInj
end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p : ∀ (p : ℕ) [Fact p.Prime] (x : O0 p), ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  first | exact @GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | exact GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | (intros; apply GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n → ∃ _ : IsDomain (On p n), IsDiscreteValuationRing (On p n) ∧ Irreducible (xn p n - 1) := by
  first | exact @GlobalTheory.K5.OnDVR.isDVR_On | exact GlobalTheory.K5.OnDVR.isDVR_On | (intros; apply GlobalTheory.K5.OnDVR.isDVR_On <;> assumption)
end

section

open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial

namespace GlobalTheory.K5.DenseAlg

theorem exists_mem_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
    (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) → ∀ (k : ℕ) (e : Ωl),
    IsInt (p := p) e → IsAlgZp (p := p) e → ∃ a ∈ A, Cong (p := p) k e (j a) := by
  intro Ω _ _ _ p hp A Ωl _ _ hclo j hA k e he halg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcong : ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
    obtain ⟨P, hP0, hP⟩ := halg
    have : CharZero Ωl := Basic.charZero_of_isClo hclo
    have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hvaluation : ∃ v : Valuation Ωl ℝ≥0, (∀ x, v x ≤ 1 ↔ IsInt (p := p) x) ∧
        v (p : Ωl) < 1 := by
      obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
      have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
        rw [hirr.maximalIdeal_eq]
        exact GlobalTheory.T.unramified_integers_adic_complete p
      have := hclo.alg
      obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
        (O0 p) Ωl hclo.inj
      refine ⟨v, hv, lt_of_le_of_ne ((hv _).2 ?_) ?_⟩
      · simpa [IsInt] using Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ)
      · intro h_eq
        have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, h_eq, inv_one]
        exact Basic.not_cong_one_zero hclo 1 one_ne_zero
          ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hpne]⟩
    obtain ⟨v, hv, hp1⟩ := hvaluation
    set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
    have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
    have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
    have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
    have hc : φ P.leadingCoeff ≠ 0 := by
      rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
      exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
    have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
    have hp0 : 0 < v (p : Ωl) := (Valuation.pos_iff v).2 hpne
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
      (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
    have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
    have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
      hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
    obtain ⟨Q, R, hdeg, hQR⟩ := Dense.exists_approx P N
    have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
      intro y hy
      rw [map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le hy
    have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
      have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
      simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
      rw [map_pow, map_natCast] at this
      exact this
    have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
      rw [eq_sub_of_add_eq hco.symm]
      exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
    have hQ0 : Q.coeff P.natDegree ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, map_zero] at hvQ
      exact hvc.ne hvQ
    have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
    have hRe : v (R.eval₂ φ e) ≤ 1 := by
      rw [eval₂_eq_sum_range]
      refine Valuation.map_sum_le v fun i _ => ?_
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
    have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
      rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
        RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
      exact eq_neg_of_add_eq_zero_left hPe
    obtain ⟨a, ha⟩ := Dense.exists_near_root v j e (v (p : Ωl) ^ k) Q (by
      rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
      exact (hsmall _ hRe).trans_lt hN)
    refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
    · rw [show j a = e - (e - j a) by ring]
      exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
    · rw [map_div₀, map_pow]
      exact div_le_one_of_le₀ ha.le zero_le
    · field_simp
  obtain ⟨a, ha, hc⟩ := hcong
  exact ⟨a, (hA a).2 ha, hc⟩

end GlobalTheory.K5.DenseAlg
end

section

open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial

theorem _root_.GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
      (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl],
      IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) →
      ∀ (k : ℕ) (e : Ωl), IsInt (p := p) e → IsAlgZp (p := p) e →
      ∃ a ∈ A, Cong (p := p) k e (j a) := by
  intro Ω _ _ _ p hp A Ωl _ _ hclo j hA k e he halg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcong : ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
    obtain ⟨P, hP0, hP⟩ := halg
    have : CharZero Ωl := Basic.charZero_of_isClo hclo
    have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    obtain ⟨v, hv, _, hp0, hp1⟩ := GlobalTheory.K5.exists_valuation_isInt p Ωl hclo
    set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
    have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
    have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
    have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
    have hc : φ P.leadingCoeff ≠ 0 := by
      rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
      exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
    have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
      (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
    have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
    have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
      hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
    obtain ⟨Q, R, hdeg, hQR⟩ := Dense.exists_approx P N
    have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
      intro y hy
      rw [map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le hy
    have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
      have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
      simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
      rw [map_pow, map_natCast] at this
      exact this
    have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
      rw [eq_sub_of_add_eq hco.symm]
      exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
    have hQ0 : Q.coeff P.natDegree ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, map_zero] at hvQ
      exact hvc.ne hvQ
    have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
    have hRe : v (R.eval₂ φ e) ≤ 1 := by
      rw [eval₂_eq_sum_range]
      refine Valuation.map_sum_le v fun i _ => ?_
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
    have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
      rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
        RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
      exact eq_neg_of_add_eq_zero_left hPe
    obtain ⟨a, ha⟩ := Dense.exists_near_root v j e (v (p : Ωl) ^ k) Q (by
      rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
      exact (hsmall _ hRe).trans_lt hN)
    refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
    · rw [show j a = e - (e - j a) by ring]
      exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
    · rw [map_div₀, map_pow]
      exact div_le_one_of_le₀ ha.le zero_le
    · field_simp
  obtain ⟨a, ha, hc⟩ := hcong
  exact ⟨a, (hA a).2 ha, hc⟩
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem one_sub_two_div_le_mass_true :
    ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 - 2 / (g : ℝ) ≤ mass g N fun _ => True := by
  intro g hg N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg.out.pos
  have hpow : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 N
  have hterm : ∀ f ∈ sqSet g N, ((g : ℝ) ^ N)⁻¹ ≤ ((torusCard g f : ℝ))⁻¹ := by
    intro f hf
    obtain ⟨h1, h2, -⟩ := (GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf
    have h1' : (0 : ℝ) < (torusCard g f : ℝ) := by exact_mod_cast h1
    have h2' : (torusCard g f : ℝ) ≤ (g : ℝ) ^ N := by exact_mod_cast h2
    exact inv_anti₀ h1' h2'
  have hsum : ((sqSet g N).card : ℝ) * ((g : ℝ) ^ N)⁻¹ ≤ mass g N fun _ => True := by
    have h := Finset.card_nsmul_le_sum (sqSet g N) (fun f => ((torusCard g f : ℝ))⁻¹) _ hterm
    rw [nsmul_eq_mul] at h
    unfold mass
    simpa only [Finset.filter_true] using h
  refine le_trans ?_ hsum
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : (1 : (ZMod g)[X]) ∈ sqSet g 0 :=
      (GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree g 0 1).2 ⟨monic_one, natDegree_one, squarefree_one, by simp⟩
    have hc : (1 : ℝ) ≤ ((sqSet g 0).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨_, h1⟩
    have : (0 : ℝ) ≤ 2 / (g : ℝ) := by positivity
    simp only [pow_zero, inv_one, mul_one]
    linarith
  · have hc := GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge g N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hc
    have he : 1 - 2 / (g : ℝ) = ((g : ℝ) ^ (M + 1) - 2 * (g : ℝ) ^ M) * ((g : ℝ) ^ (M + 1))⁻¹ := by
      field_simp
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hc (inv_nonneg.2 hpow.le)

end GlobalTheory.BadShare
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.squarefreeLabelMass_degreeType_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (μ : Multiset ℕ), (mass g N fun f => degType g f = μ) ≤ (∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * (μ.count d).factorial))⁻¹ := by
  first | exact @GlobalTheory.BadShare.mass_degType_le | exact GlobalTheory.BadShare.mass_degType_le | (intros; apply GlobalTheory.BadShare.mass_degType_le <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.card_generalLinearGroup_primeField : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), Fintype.card (GG g N) = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  first | exact @GlobalTheory.BadShare.card_GG_eq | exact GlobalTheory.BadShare.card_GG_eq | (intros; apply GlobalTheory.BadShare.card_GG_eq <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.exteriorTensorProduct_convolution_calculus : ∀ (ι G G' : Type) [Fintype ι] [Group G] [Fintype G] [Group G'] [Fintype G'], (∀ a b : ι → G → ℂ, conv (tens a) (tens b) = tens fun v => conv (a v) (b v)) ∧ (∀ a : ι → G → ℂ, (∀ v, IsProj (a v)) → IsProj (tens a)) ∧ (∀ (a a' : G → ℂ) (b b' : G' → ℂ), conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b')) ∧ (∀ (a : G → ℂ) (b : G' → ℂ), IsProj a → IsProj b → IsProj (tens2 a b)) ∧ tens2 (dirac : G → ℂ) (dirac : G' → ℂ) = dirac ∧ ∀ (a a' : G → ℂ) (b b' : G' → ℂ), tens2 (a - a') b = tens2 a b - tens2 a' b ∧ tens2 a (b - b') = tens2 a b - tens2 a b' := by
  first | exact @GlobalTheory.BadShare.tens_calculus | exact GlobalTheory.BadShare.tens_calculus | (intros; apply GlobalTheory.BadShare.tens_calculus <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.card_levelDatum_group_mul_pow : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  first | exact @GlobalTheory.BadShare.lev_card | exact GlobalTheory.BadShare.lev_card | (intros; apply GlobalTheory.BadShare.lev_card <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.groupAlgebraOperator_convolution_calculus : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), (∀ a b : G → ℂ, op ρ (conv a b) = op ρ a * op ρ b ∧ op ρ (a - b) = op ρ a - op ρ b ∧ op ρ (a + b) = op ρ a + op ρ b) ∧ op ρ dirac = 1 ∧ (∀ a b c : G → ℂ, conv (conv a b) c = conv a (conv b c) ∧ conv (a - b) c = conv a c - conv b c ∧ conv c (a - b) = conv c a - conv c b) ∧ (∀ a : G → ℂ, conv dirac a = a ∧ conv a dirac = a) ∧ (∀ a b : G → ℂ, IsProj a → IsProj b → conv a b = conv b a → IsProj (conv a b)) ∧ (∀ a : G → ℂ, IsProj a → IsProj (dirac - a)) ∧ ∀ e : G → ℂ, conv e e = e → (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  first | exact @GlobalTheory.BadShare.convCalc | exact GlobalTheory.BadShare.convCalc | (intros; apply GlobalTheory.BadShare.convCalc <;> assumption)
end
