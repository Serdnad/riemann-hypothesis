module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle094
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem jT_invariant (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ :=
  ReciprocityTheory.ChartRestriction.L1.jT_smul γ τ

theorem DD_mul_jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD τ * jT (γ • τ) = E₄ τ ^ 3 := by
  rw [jT_invariant, jT, ReciprocityTheory.ChartRestriction.L1.AA, mul_div_cancel₀ _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)]

theorem jT_level_one : ∀ E : Subring ℂ, Lv E 1 1 jT ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), jT (γ • τ) = jT τ := by
  intro E
  refine ⟨⟨fun γ _ τ => jT_invariant γ τ, fun γ => ?_⟩, jT_invariant⟩
  have hE4 : QAll (· ∈ E) 1 ⇑E₄ := ((eis_q 1 one_pos _ (Or.inl rfl)).2.1) E
  have h3 : QAll (· ∈ E) 1 fun τ => E₄ τ ^ 3 := (QAllSubring.ring_closed E 1 one_pos).2.2.2.2.1 _ 3 hE4
  have hfun : (fun τ => DD τ ^ 1 * jT (γ • τ)) = fun τ => E₄ τ ^ 3 := by
    funext τ; rw [pow_one, DD_mul_jT_smul]
  rw [hfun]; exact h3

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCongLift

theorem cong_of_dvd {M N : ℕ} (hMN : M ∣ N) {d : ℤ} {γ γ' : SL(2, ℤ)} (h : Cong N d γ γ') : Cong M d γ γ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have key : ∀ x y : ZMod N, x = y → ZMod.castHom hMN (ZMod M) x = ZMod.castHom hMN (ZMod M) y :=
    fun x y hxy => by rw [hxy]
  have k1 := key _ _ h1
  have k2 := key _ _ h2
  have k3 := key _ _ h3
  have k4 := key _ _ h4
  simp only [map_mul, map_intCast] at k1 k2 k3 k4
  exact ⟨k1, k2, k3, k4⟩

theorem cong_congr_d {M : ℕ} {d d' : ℤ} (h : (d : ZMod M) = d') {γ γ' : SL(2, ℤ)} (hc : Cong M d γ γ') :
    Cong M d' γ γ' := by
  unfold Cong at hc ⊢
  rw [← h]
  exact hc

theorem en_eq_of_cong {M : ℕ} {d : ℤ} (hd : IsUnit (d : ZMod M)) {γ γ' γ'' : SL(2, ℤ)}
    (h' : Cong M d γ γ') (h'' : Cong M d γ γ'') :
    ∀ i j, (en γ' i j : ZMod M) = en γ'' i j := by
  obtain ⟨a1, a2, a3, a4⟩ := h'
  obtain ⟨b1, b2, b3, b4⟩ := h''
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; rw [a1, b1]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [a2, b2]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    exact hd.mul_left_cancel (a3.trans b3.symm)
  · simp only [Fin.isValue, Fin.mk_one]; rw [a4, b4]

theorem mem_Gamma_iff_en {M : ℕ} (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma M ↔
      (en γ 0 0 : ZMod M) = 1 ∧ (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [en]

theorem mul_inv_mem_Gamma {M : ℕ} {γ' γ'' : SL(2, ℤ)} (h : ∀ i j, (en γ' i j : ZMod M) = en γ'' i j) :
    γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'' := by
    ext i j
    simpa [en] using h i j
  rw [map_mul, map_inv, this, mul_inv_cancel]

theorem cong_lift : ∀ (M N : ℕ) (d d' : ℤ), 0 < N → M ∣ N → (d : ZMod M) = d' → IsUnit (d' : ZMod N) → (∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → ∃ γ'' : SL(2, ℤ), Cong N d' γ γ'' ∧ γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M) ∧ ∀ δ' ∈ CongruenceSubgroup.Gamma M, ∃ δ ∈ CongruenceSubgroup.Gamma M, Cong N d' δ δ' := by
  intro M N d d' hN hMN hdd' hu
  haveI : NeZero N := ⟨hN.ne'⟩
  have hdM : IsUnit (d : ZMod M) := by
    have := (hu.map (ZMod.castHom hMN (ZMod M)))
    rw [hdd']; simpa using this
  have hdM' : (d' : ZMod M) = d := hdd'.symm
  obtain ⟨u, hu'⟩ := hu
  obtain ⟨ex1, ex2⟩ := GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N u
  refine ⟨fun γ γ' hγ => ?_, fun δ' hδ' => ?_⟩
  · obtain ⟨γ'', hγ''⟩ := ex1 γ
    have hc : Cong N d' γ γ'' := (GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d' u hu' γ γ'').2 hγ''
    refine ⟨γ'', hc, mul_inv_mem_Gamma (en_eq_of_cong hdM hγ ?_)⟩
    exact cong_congr_d hdM' (cong_of_dvd hMN hc)
  · obtain ⟨δ, hδ⟩ := ex2 δ'
    have hc : Cong N d' δ δ' := (GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d' u hu' δ δ').2 hδ
    refine ⟨δ, ?_, hc⟩
    have hcM := cong_congr_d hdM' (cong_of_dvd hMN hc)
    obtain ⟨c1, c2, c3, c4⟩ := hcM
    obtain ⟨g1, g2, g3, g4⟩ := (mem_Gamma_iff_en δ').1 hδ'
    rw [mem_Gamma_iff_en]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← c1, g1]
    · have : (d : ZMod M) * en δ 0 1 = d * 0 := by rw [← c2, g2, mul_zero]
      exact hdM.mul_left_cancel this
    · rw [← c3, g3, mul_zero]
    · rw [← c4, g4]

end GlobalTheory.FNCongLift
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_integral_cuspExpansion_jInvariant : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  first | exact @GlobalTheory.FNExpJ.expansion_j | exact GlobalTheory.FNExpJ.expansion_j | (intros; apply GlobalTheory.FNExpJ.expansion_j <;> assumption)
end

section

open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem ffMu_eq (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a₀ : ℤ) (s : ℕ) :
    ffMu N p m k ψ a₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ a₀ [ZMOD N] then
        (q.2.sign : K) * (ψ (q.1 : ZMod (p ^ m)) * (q.1 : K) ^ (k - 2)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ a₀ [ZMOD N] then
        (d.sign : K) * (ψ (A : ZMod (p ^ m)) * (A : K) ^ (k - 2)) else 0)]
  unfold ffMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem eeMu_eq (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b₀ : ℤ) (s : ℕ) :
    eeMu N p m ψ b₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ b₀ [ZMOD N] then
        (q.2.sign : K) * ψ⁻¹ (q.2 : ZMod (p ^ m)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ b₀ [ZMOD N] then
        (d.sign : K) * ψ⁻¹ (d : ZMod (p ^ m)) else 0)]
  unfold eeMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem drop_const (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y y₁ y₂ : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) := by
  have hp : p.Prime := Fact.out
  by_cases hi : i = 0
  · subst hi
    have hk1 : k - 1 ≠ 1 := by omega
    simp only [eisF, const0, if_true, if_neg hk1]
    rw [sum_zero_left p m hm ψ hψ]
    simp [coefPos]
  by_cases hj : j = 0
  · subst hj
    have e : ∀ v ∈ primeTo p m, ∀ z : ℤ, eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) z 0 =
        ((1 / 2 - frc (N * p ^ m) (N * v.val + (p : ℤ) ^ m * y) : ℚ) : K) := by
      intro v hv z
      have : ¬ ((N * p ^ m : ℕ) : ℤ) ∣ N * v.val + (p : ℤ) ^ m * y := by
        intro h
        have h1 : (p : ℤ) ^ m ∣ N * v.val + (p : ℤ) ^ m * y :=
          (show (p : ℤ) ^ m ∣ ((N * p ^ m : ℕ) : ℤ) by push_cast; exact dvd_mul_left _ _).trans h
        have h2 : (p : ℤ) ∣ (N : ℤ) * v.val := by
          have := dvd_sub h1 (dvd_mul_right ((p : ℤ) ^ m) y)
          rw [add_sub_cancel_right] at this
          exact (dvd_pow_self (p : ℤ) (by omega)).trans this
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2 with h3 | h3
        · exact hpN (Int.natCast_dvd_natCast.mp h3)
        · exact (mem_filter.mp hv).2 (Int.natCast_dvd_natCast.mp h3)
      simp only [eisF, const0, if_true, if_neg this]
    rw [sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun v hv => sum_congr rfl fun b _ => by
      rw [e v hv], sum_zero_right p m hm ψ hψ]
    simp [coefPos]
  simp only [eisF, if_neg hi, if_neg hj]

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  first | exact @GlobalTheory.FN.inR_mdifferentiable | exact GlobalTheory.FN.inR_mdifferentiable | (intros; apply GlobalTheory.FN.inR_mdifferentiable <;> assumption)
end

section

open Polynomial

namespace GlobalTheory.K4

theorem kum_congr_base {K₁ K₂ Ω : Type*} [Field K₁] [Field K₂] [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω] {N : ℕ}
    (ζ θ : Ω) (g : Ω ≃ₐ[K₁] Ω) (g' : Ω ≃ₐ[K₂] Ω) (h : ∀ x, g x = g' x) :
    GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum (N := N) ζ θ g' := by
  have e : g θ = g' θ := h θ
  unfold GlobalTheory.NeedB.kum
  rw [e]

theorem valuation_eq_one_of_mem_inv_mem {Ω : Type*} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B)
    (hx' : x⁻¹ ∈ B) (h0 : x ≠ 0) : B.valuation x = 1 := by
  have h1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
  have h2 : B.valuation x⁻¹ ≤ 1 := (B.valuation_le_one_iff _).2 hx'
  have h3 : B.valuation x * B.valuation x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = B.valuation x * B.valuation x⁻¹ := h3.symm
    _ ≤ B.valuation x * 1 := by gcongr
    _ = B.valuation x := mul_one _

theorem mem_of_isIntegral_of_le {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω] (B : ValuationSubring Ω)
    (hB : ∀ p : R, algebraMap R Ω p ∈ B) {x : Ω} (hx : IsIntegral R x) : x ∈ B := by
  obtain ⟨p, hpm, hp⟩ := hx
  let φ : R →+* B := (algebraMap R Ω).codRestrict B hB
  have hcomp : (algebraMap B Ω).comp φ = algebraMap R Ω := by
    ext r
    rfl
  have hB' : IsIntegral B x := ⟨p.map φ, hpm.map φ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := Ω)).1 hB'
  rw [← hy]
  exact y.2

theorem thmA_on_open_geo : GlobalTheory.NeedB.ThmA → ∀ (k F Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field Ω] [Algebra F (RatFunc k)] [Algebra (RatFunc k) Ω] [Algebra F Ω] [IsScalarTower F (RatFunc k) Ω] [Algebra k[X] Ω] [IsScalarTower k[X] (RatFunc k) Ω] [IsAlgClosure (RatFunc k) Ω] [Algebra.IsAlgebraic F Ω] (N : ℕ) [NeZero N] (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (U : Subgroup (Ω ≃ₐ[F] Ω)), IsOpen (U : Set (Ω ≃ₐ[F] Ω)) → ∀ α β : Ω, α ≠ 0 → β ≠ 0 → IsIntegral k[X] α → IsIntegral k[X] α⁻¹ → IsIntegral k[X] β → IsIntegral k[X] β⁻¹ →
 (∀ g ∈ U, g (α ^ N) = α ^ N ∧ g (β ^ N) = β ^ N) →
 ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N, IsLocallyConstant (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) ∧
  (∀ g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ h ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, GlobalTheory.NeedB.kum (N := N) ζ α g * GlobalTheory.NeedB.kum ζ β h = η₀ h - η₀ (g * h) + η₀ g) ∧
  ∀ r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ B : ValuationSubring Ω, (∀ p : k[X], algebraMap k[X] Ω p ∈ B) → GlobalTheory.NeedB.Inert B r → η₀ r = 0 ∧ r α = α ∧ r β = β := by
  intro hA k F Ω _ _ _ _ _ _ _ _ _ _ _ _ _ N _ ζ hζ U hU α β hα0 hβ0 hαi hαi' hβi hβi' hUfix
  classical
  obtain ⟨-, ⟨e, he, hec, -⟩, -, -, -⟩ := GlobalTheory.T.fixingSubgroupOfIntermediateField_properties F (RatFunc k) Ω
  let U' : Subgroup (Ω ≃ₐ[RatFunc k] Ω) :=
    U.comap ((GlobalTheory.K4.geo F (RatFunc k) Ω).subtype.comp e.toMonoidHom)
  have hU'mem : ∀ g, g ∈ U' ↔ ((e g : GlobalTheory.K4.geo F (RatFunc k) Ω) : Ω ≃ₐ[F] Ω) ∈ U := fun g => Iff.rfl
  have hU'open : IsOpen (U' : Set (Ω ≃ₐ[RatFunc k] Ω)) :=
    (continuous_subtype_val.comp hec).isOpen_preimage _ hU
  let K' : IntermediateField (RatFunc k) Ω := IntermediateField.fixedField U'
  have hfixle : U' ≤ K'.fixingSubgroup := (IntermediateField.le_iff_le U' K').1 le_rfl
  haveI : FiniteDimensional (RatFunc k) K' :=
    (InfiniteGalois.isOpen_iff_finite K').1 (Subgroup.isOpen_mono hfixle hU'open)
  haveI : IsScalarTower F K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k[X] K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAlgClosure K' Ω :=
    ⟨IsAlgClosure.isAlgClosed (RatFunc k), Algebra.IsAlgebraic.tower_top (K := RatFunc k) K'⟩
  obtain ⟨-, ⟨e', he', -, hesc'⟩, -, -, -⟩ := GlobalTheory.T.fixingSubgroupOfIntermediateField_properties F K' Ω
  have hφ : ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω) x, (e'.symm ⟨g, hg⟩) x = g x := by
    intro g hg x
    have := he' (e'.symm ⟨g, hg⟩) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hsub : ∀ g, g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U → g ∈ GlobalTheory.K4.geo F K' Ω := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    rw [GlobalTheory.K4.TopW.mem_geo]
    intro x
    have h1 : e.symm ⟨g, hg.1⟩ ∈ U' := by
      rw [hU'mem, MulEquiv.apply_symm_apply]
      exact hg.2
    have h2 := (IntermediateField.mem_fixedField_iff U' (x : Ω)).1 x.2 _ h1
    have h3 : (e.symm ⟨g, hg.1⟩) (x : Ω) = g x := by
      have := he (e.symm ⟨g, hg.1⟩) (x : Ω)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [IntermediateField.algebraMap_apply, ← h3]
    exact h2
  have hfixK' : ∀ z : Ω, (∀ g ∈ U, g z = z) → z ∈ K' := by
    intro z hz
    refine (IntermediateField.mem_fixedField_iff U' z).2 fun f hf => ?_
    have := hz _ ((hU'mem f).1 hf)
    rw [he] at this
    exact this
  have hαK : α ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).1
  have hβK : β ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).2
  have hint : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ →
      (⟨θ ^ N, hθ⟩ : K') ∈ FunctionField.ringOfIntegers k K' ∧
        (⟨θ ^ N, hθ⟩ : K')⁻¹ ∈ FunctionField.ringOfIntegers k K' := by
    intro θ hθ h1 h2
    constructor
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (B := Ω)).1 ?_
      exact h1.pow N
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (B := Ω)).1 ?_
      rw [map_inv₀, IntermediateField.algebraMap_apply, ← inv_pow]
      exact h2.pow N
  have hne : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), θ ≠ 0 → (⟨θ ^ N, hθ⟩ : K') ≠ 0 := by
    intro θ hθ h0 h
    exact pow_ne_zero N h0 (congrArg Subtype.val h)
  obtain ⟨-, -, -, -, η, hηlc, hηco, hηin⟩ :=
    hA k K' Ω N ζ (Nat.pos_of_ne_zero (NeZero.ne N)) hζ ⟨α ^ N, hαK⟩ ⟨β ^ N, hβK⟩ α β (hne hαK hα0) (hne hβK hβ0)
      (hint hαK hαi hαi').1 (hint hαK hαi hαi').2 (hint hβK hβi hβi').1 (hint hβK hβi hβi').2 rfl rfl
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N,
      ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω), η₀ g = η (e'.symm ⟨g, hg⟩) :=
    ⟨fun g => if hg : g ∈ GlobalTheory.K4.geo F K' Ω then η (e'.symm ⟨g, hg⟩) else 0, fun g hg => dif_pos hg⟩
  refine ⟨η₀, ?_, ?_, ?_⟩
  · have hfun : (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) =
        η ∘ e'.symm ∘ (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => (⟨g.1, hsub _ g.2⟩ : GlobalTheory.K4.geo F K' Ω)) := by
      funext g
      exact hη₀ _ _
    rw [hfun]
    exact hηlc.comp_continuous (hesc'.comp (continuous_subtype_val.subtype_mk _))
  · intro g hg h hh
    have hgh := mul_mem hg hh
    rw [hη₀ _ (hsub _ hg), hη₀ _ (hsub _ hh), hη₀ _ (hsub _ hgh),
      kum_congr_base ζ α g (e'.symm ⟨g, hsub _ hg⟩) (fun x => (hφ _ _ x).symm),
      kum_congr_base ζ β h (e'.symm ⟨h, hsub _ hh⟩) (fun x => (hφ _ _ x).symm)]
    have hm : e'.symm ⟨g * h, hsub _ hgh⟩ = e'.symm ⟨g, hsub _ hg⟩ * e'.symm ⟨h, hsub _ hh⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    exact hηco _ _
  · intro r hr B hB hinert
    have hmemB : ∀ {x : Ω}, IsIntegral k[X] x → x ∈ B := fun hx => mem_of_isIntegral_of_le B hB hx
    have hNk : (N : k) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have hk : (N : k[X]) * C ((N : k)⁻¹) = 1 := by
      rw [← map_natCast C N, ← C_mul, mul_inv_cancel₀ hNk, C_1]
    have h1 : (N : Ω) * algebraMap k[X] Ω (C ((N : k)⁻¹)) = 1 := by
      rw [← map_natCast (algebraMap k[X] Ω) N, ← map_mul, hk, map_one]
    have hNΩ : (N : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hvN : B.valuation (N : Ω) = 1 := by
      refine valuation_eq_one_of_mem_inv_mem B ?_ ?_ hNΩ
      · rw [← map_natCast (algebraMap k[X] Ω) N]
        exact hB _
      · rw [← eq_inv_of_mul_eq_one_right h1]
        exact hB _
    have hroot : ∀ θ : Ω, θ ≠ 0 → IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ → r (θ ^ N) = θ ^ N → r θ = θ := by
      intro θ h0 hi hi' hfix
      refine GlobalTheory.T.inert_apply_eq_of_pow_fixed_of_valuation_one F Ω B r N 1 θ (Nat.pos_of_ne_zero (NeZero.ne N)) hvN hinert (map_one r) one_ne_zero hfix ?_
      rw [one_pow, div_one]
      refine valuation_eq_one_of_mem_inv_mem B (hmemB (hi.pow N)) ?_ (pow_ne_zero N h0)
      rw [← inv_pow]
      exact hmemB (hi'.pow N)
    rw [Subgroup.mem_inf] at hr
    refine ⟨?_, hroot α hα0 hαi hαi' (hUfix r hr.2).1, hroot β hβ0 hβi hβi' (hUfix r hr.2).2⟩
    have hr' : r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U := Subgroup.mem_inf.2 hr
    rw [hη₀ _ (hsub _ hr')]
    refine hηin B ?_ _ ?_
    · intro x hx
      refine hmemB ?_
      exact ((mem_integralClosure_iff _ _).1 hx).algebraMap
    · intro x hx
      rw [hφ]
      exact hinert x hx

end GlobalTheory.K4
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.compactSubgroupSmoothCharacterDatum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  first | exact @GlobalTheory.StripGrp.strip_datum_monotone | exact GlobalTheory.StripGrp.strip_datum_monotone | (intros; apply GlobalTheory.StripGrp.strip_datum_monotone <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_isOpen_isCompact | exact GlobalTheory.PsType.grp_isOpen_isCompact | (intros; apply GlobalTheory.PsType.grp_isOpen_isCompact <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  first | exact @GlobalTheory.PsType.theta_one_and_near | exact GlobalTheory.PsType.theta_one_and_near | (intros; apply GlobalTheory.PsType.theta_one_and_near <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.modularTower_class_eq_imp_pow_ratio : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ), X.cls l n f = X.cls l n f' → ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.Tower.cls_eq_pow | exact GlobalTheory.Tower.cls_eq_pow | (intros; apply GlobalTheory.Tower.cls_eq_pow <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, a⁻¹ ∈ grp ψ := by
  first | exact @GlobalTheory.PsType.grp_inv_mem | exact GlobalTheory.PsType.grp_inv_mem | (intros; apply GlobalTheory.PsType.grp_inv_mem <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  first | exact @GlobalTheory.PsType.corner_rankOne | exact GlobalTheory.PsType.corner_rankOne | (intros; apply GlobalTheory.PsType.corner_rankOne <;> assumption)
end
