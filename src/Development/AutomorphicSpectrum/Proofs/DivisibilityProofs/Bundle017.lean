module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle013
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle003
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle005
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem mixDiff_mul_leibniz {σ : Type} (A B : MvPolynomial σ ℝ) :
    mixDiff (A * B) = mixDiff A * rename Sum.inl B + rename Sum.inr A * mixDiff B := by
  simp only [mixDiff, map_mul]
  ring

theorem mixDiff_eq_zero_of_isHomogeneous_zero {σ : Type} {Q : MvPolynomial σ ℝ}
    (hQ : Q.IsHomogeneous 0) : mixDiff Q = 0 := by
  have h : Q.totalDegree = 0 := Nat.eq_zero_of_le_zero hQ.totalDegree_le
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h
  rw [h]
  simp only [mixDiff, rename_C, sub_self]

theorem rootPs_mul_mixExpansion : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ), Q.IsHomogeneous (d + 1 - k) → ∃ Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ, (∀ i, (Hs i).IsHomogeneous (d - k)) ∧ (k = d + 1 → ∀ i, Hs i = 0) ∧ IsMixExpansion d (mixDiff (rootPs τ k * Q)) (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) := by
  intro Ψ _ _ N d k hk1 hk2 τ Q hQ
  obtain ⟨Hs, hMix⟩ := GlobalTheory.T.exists_mixed_difference_expansion (Ψ × Fin N) (d + 1 - k) Q hQ
  unfold IsMixExpansion at hMix
  obtain ⟨hHs, hHdeg⟩ := hMix
  have hQl : (rename Sum.inl Q : MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ).IsHomogeneous (d + 1 - k) :=
    hQ.rename_isHomogeneous
  have hE := GlobalTheory.T.power_sum_mixed_expansion (Ψ × Fin N) N k (d + 1 - k) (fun a => (τ, a)) (rename Sum.inl Q) hQl
  unfold IsMixExpansion at hE
  obtain ⟨hE1, hE2⟩ := hE
  obtain ⟨Hs', hz, hmixQ, hdeg'⟩ : ∃ Hs' : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ,
      (k = d + 1 → ∀ i, Hs' i = 0) ∧ mixDiff Q = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Hs' i ∧
        ∀ i, (Hs' i).IsHomogeneous (d - k) := by
    by_cases hkd : k = d + 1
    · refine ⟨fun _ => 0, fun _ _ => rfl, ?_, fun _ => MvPolynomial.isHomogeneous_zero _ _ _⟩
      have h0 : Q.IsHomogeneous 0 := by
        have e : d + 1 - k = 0 := by omega
        rw [e] at hQ
        exact hQ
      simp only [mul_zero, Finset.sum_const_zero]
      exact mixDiff_eq_zero_of_isHomogeneous_zero h0
    · refine ⟨Hs, fun h => absurd h hkd, hHs, fun i => ?_⟩
      have h3 := hHdeg i
      have e : d + 1 - k - 1 = d - k := by omega
      rw [e] at h3
      exact h3
  unfold IsMixExpansion
  refine ⟨Hs', hdeg', hz, ?_, ?_⟩
  · rw [mixDiff_mul_leibniz, hmixQ]
    have h1 : mixDiff (rootPs τ k : MvPolynomial (Ψ × Fin N) ℝ) * rename Sum.inl Q =
        ∑ i, (X (Sum.inl i) - X (Sum.inr i)) *
          ((∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i),
            rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a)))
              (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q) := hE1
    have h2 : (rename Sum.inr (rootPs τ k : MvPolynomial (Ψ × Fin N) ℝ) :
        MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ) = ∑ a : Fin N, X (Sum.inr (τ, a)) ^ k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rootPs, map_sum, map_pow, rename_X]
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · intro i
    apply MvPolynomial.IsHomogeneous.add
    · have h4 := hE2 i
      have e : k - 1 + (d + 1 - k) = d := by omega
      rw [e] at h4
      exact h4
    · have hS : (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k :
          MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ).IsHomogeneous k :=
        MvPolynomial.IsHomogeneous.sum _ _ _ (fun a _ => MvPolynomial.isHomogeneous_X_pow _ _)
      by_cases hkd : k = d + 1
      · rw [hz hkd i, mul_zero]
        exact MvPolynomial.isHomogeneous_zero _ _ _
      · have h5 := hS.mul (hdeg' i)
        have e : k + (d - k) = d := by omega
        rw [e] at h5
        exact h5

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.local_pair_value_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)), (∀ Gs Hs, T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧ (∀ (c : ℝ) Gs, T.val P (fun i => C c * Gs i) = c * T.val P Gs) ∧ ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => ∑ a ∈ s, Gs a i) = ∑ a ∈ s, T.val P (Gs a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.locPair_val_linear | exact GlobalTheory.CompanionTheory.Ar.Num.locPair_val_linear | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.locPair_val_linear <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.cycle_number_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.cycle_number_rename : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.numbers_rename | exact GlobalTheory.CompanionTheory.Ar.Num.numbers_rename | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.numbers_rename <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycNum_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * cycNum Z cls H (classList cls μ ++ Q) := by
  exact @BaseChangeColon.cycNum_mul_expansion

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_mul_expand : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) :=
  @BaseChangeColon.genNum_mul_expansion

end GlobalTheory.CompanionTheory.Ar.Num
end

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem eval_formPoly_none_zero {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (PB.formPoly n a) =
      eval c (PB.formPoly n fun w => a fun j => some (w j)) := by
  have h : ∀ Q : MvPolynomial (Option σ) ℝ,
      eval c (aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) Q) =
        eval (fun o : Option σ => o.elim 0 c) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p o hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases o <;> simp
  rw [← h, PB.killNone_formPoly]

theorem linA_zero_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (k : ℕ) :
    linA lam 0 ^ k = toA (linRoot lam ^ k) := by
  simp [linA, toA, map_pow]

theorem swapWt_uncurry {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (lam : Wt Ψ N) :
    (fun x : Ψ × Fin N => swapWt τ a b lam x.1 x.2) =
      (fun x : Ψ × Fin N => lam x.1 x.2) ∘ Equiv.swap (τ, a) (τ, b) := by
  funext ⟨σ, i⟩
  by_cases hσ : σ = τ
  · subst hσ
    by_cases h1 : i = a
    · subst h1; simp [swapWt]
    · by_cases h2 : i = b
      · subst h2; simp [swapWt]
      · simp [swapWt, Equiv.swap_apply_def, h1, h2]
  · simp [swapWt, Equiv.swap_apply_def, hσ]

theorem eval_rho_antisymDelta_ne {Ψ : Type} [Fintype Ψ] {N : ℕ} :
    eval (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) ≠ 0 := by
  simp only [GroundTheory.Heights₂.Heights.antisymDelta, map_prod, map_sub, eval_X]
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun a _ =>
    Finset.prod_ne_zero_iff.2 fun b hb => ?_
  have hab : a < b := Finset.mem_Ioi.1 hb
  have hab' : (a : ℕ) < b := hab
  have : ((a : ℕ) : ℝ) < b := by exact_mod_cast hab'
  simp only [rhoWt]
  intro h
  linarith

end GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem Realis_PB_gapS_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type} [Fintype σ]
    {S : PB.AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (II : IntersectionSystem) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (Re.PB II) = eval c ((Re.comap some).PB II) :=
  eval_formPoly_none_zero _ _ c

theorem AnSys_degPoly_gapS_zero {D : ℕ} {σ : Type} [Fintype σ] (S : PB.AnSys D (Option σ)) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) S.degPoly = eval c (S.comap some).degPoly :=
  eval_formPoly_none_zero _ _ c

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem log_div_pred_le_of_lt (B p : ℕ) (hB : 128 ≤ B) (hp : B < p) (hL : 1 ≤ Real.log ((B : ℝ) + 1)) :
    Real.log p / ((p : ℝ) - 1) ≤ Real.log ((B : ℝ) + 1) / B := by
  have hB0 : (0 : ℝ) < B := by
    have : (128 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hpB : (B : ℝ) + 1 ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : Real.log p ≤ Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hB1)
    rw [Real.log_div hp0.ne' hB1.ne'] at h1
    have h2 : (p : ℝ) / ((B : ℝ) + 1) - 1 = ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
      field_simp
      ring
    linarith
  rw [div_le_div_iff₀ hp1 hB0]
  have hd : (0 : ℝ) ≤ (p : ℝ) - B - 1 := by linarith
  have hfrac : (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1)) ≤ ((p : ℝ) - B - 1) * Real.log ((B : ℝ) + 1) := by
    have h3 : (B : ℝ) / ((B : ℝ) + 1) ≤ Real.log ((B : ℝ) + 1) := by
      refine le_trans ?_ hL
      rw [div_le_one hB1]
      linarith
    calc (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1))
        = ((p : ℝ) - B - 1) * ((B : ℝ) / ((B : ℝ) + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hd
  have h4 : Real.log p * B ≤ (Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1)) * B :=
    mul_le_mul_of_nonneg_right hlog hB0.le
  nlinarith [h4, hfrac]

theorem sum_log_div_pred_SB :
    ∀ (B : ℕ) (bad S : Finset ℕ), 128 ≤ B → bad.card ≤ B →
      (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ bad)) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  intro B bad S hB hcard hS
  have hBR : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hlogB : (4.85 : ℝ) ≤ Real.log B := by
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 128 ≤ Real.log B := Real.log_le_log (by norm_num) hBR
    rw [h128] at h3
    norm_num at h2 ⊢
    linarith
  have hLle : Real.log ((B : ℝ) + 1) ≤ Real.log B + 1 / B := by
    have hpos : (0 : ℝ) < ((B : ℝ) + 1) / B := by positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) hB0.ne'] at h1
    have h2 : ((B : ℝ) + 1) / B - 1 = 1 / B := by
      field_simp
      ring
    linarith
  have hLge : 1 ≤ Real.log ((B : ℝ) + 1) := by
    have : Real.log B ≤ Real.log ((B : ℝ) + 1) := Real.log_le_log hB0 (by linarith)
    norm_num at hlogB
    linarith
  have hinv : 1 / (B : ℝ) ≤ 1 := by
    rw [div_le_one hB0]
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ S.filter (fun p => p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 17 / 5 := by
    refine GlobalTheory.CompanionTheory.Ar.Small.sum_log_div_pred_le (B : ℝ) _ (by linarith) ?_
    intro p hp
    obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hpS).1, by exact_mod_cast hpB⟩
  have hlarge : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log ((B : ℝ) + 1) := by
    have hsub : S.filter (fun p => ¬ p ≤ B) ⊆ bad := by
      intro p hp
      obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
      exact (hS p hpS).2.resolve_left hpB
    have hc : (S.filter (fun p => ¬ p ≤ B)).card ≤ B :=
      (Finset.card_le_card hsub).trans hcard
    have h1 : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
        ≤ (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B) := by
      refine Finset.sum_le_card_nsmul _ _ _ ?_
      intro p hp
      exact log_div_pred_le_of_lt B p hB (not_le.mp (Finset.mem_filter.mp hp).2) hLge
    have h2 : (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B)
        ≤ (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) := by
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right (by exact_mod_cast hc) ?_
      exact div_nonneg (by linarith) hB0.le
    have h3 : (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) = Real.log ((B : ℝ) + 1) := by
      field_simp
    linarith
  norm_num at hlogB
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_combLine : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) :=
  @RootFieldNumerics.intersection_multilinear_one_position

end GlobalTheory.CompanionTheory.Ar.Top
end
