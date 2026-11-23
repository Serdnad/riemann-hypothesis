module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle075
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices.CocBound

theorem _root_.GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ), Γ.FiniteIndex → FiniteDimensional ℂ E → 0 < m → g ^ m = 1 → A ^ m = 1 → (∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) → FiniteDimensional ℂ (twInv Γ g A) ∧ Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices.CocBound

theorem _root_.GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 2 = t ^ 3 → Subgroup.closure ({s, t} : Set G) = ⊤ → FiniteDimensional ℂ E → FiniteDimensional ℂ (relThree Γ ρ t) → FiniteDimensional ℂ (extn Γ ρ s) ∧ Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices.CocBound

theorem _root_.GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 4 = 1 → FiniteDimensional ℂ (extn Γ ρ s) → FiniteDimensional ℂ (cocyc Γ ρ) ∧ Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s)) ≤ Module.finrank ℂ (extn Γ ρ s) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices.CocBound

theorem _root_.GlobalTheory.T.finrank_orderThreeRelation_add_twistedInvariant_le : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) → FiniteDimensional ℂ (relThree Γ ρ t) ∧ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤ Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame Asymptotics
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

private theorem slash_finset_sum {ι : Type*} (t : Finset ι) (k : ℤ) (f : ι → ℍ → ℂ) (x : SL(2, ℤ)) :
    (∑ i ∈ t, f i) ∣[k] x = ∑ i ∈ t, (f i) ∣[k] x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

private theorem tendsto_exp_neg_im :
    Tendsto (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) atImInfty (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  exact h.const_mul_atTop_of_neg (by linarith [Real.pi_pos])

theorem reduces_of_det_leadM_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s →
    (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det = 0 → Reduces Γ w F := by
  classical
  intro M Γ r s w F hM hΓ hs hF hdet
  obtain ⟨c, hc, hcv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hT := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  have hb : ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → ∑ j, c j * co M (w j) (F j) x n = 0 := by
    refine GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero M Γ r s (fun x n => ∑ j, c j * co M (w j) (F j) x n) hM hs ?_ ?_ ?_ ?_
    · intro x n
      simp only [fun j => (hT j).1 x n, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro γ hγ x n
      simp only [fun j => (hT j).2.1 γ hγ x n]
    · intro x n
      simp only [fun j => (hT j).2.2 (hF j).1 x n, mul_neg, Finset.sum_neg_distrib]
    · intro i
      have := congrFun hcv i
      simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply, Pi.zero_apply, Finset.sum_mul] at this
      rw [Finset.sum_comm, ← this]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hO : ∀ x : SL(2, ℤ), (fun τ : ℍ => ∑ j, c j * (F j ∣[w j] x) τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 := IsBigO.sum (s := Finset.univ) fun j _ =>
      (GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 x).const_mul_left (c j)
    refine h1.congr_left fun τ => ?_
    simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm, sub_eq_self]
    refine Finset.sum_eq_zero fun n hn => ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hb x n (Finset.mem_range.mp hn), zero_mul]
  have hne : (Finset.univ.filter fun j => c j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    exact ⟨j, by simpa using hj⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image _ w hne
  have hc₀ : c j₀ ≠ 0 := by simpa using hj₀
  have he : ∀ j, ∃ e : ℍ → ℂ, IsMF ⊤ (w j₀ - w j + 4) e ∧
      (fun τ : ℍ => e τ - c j) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro j
    by_cases hj : c j = 0
    · exact ⟨0, IsMF.zero _ _, by simp [hj, isBigO_zero]⟩
    · have hle : w j ≤ w j₀ := hmax j (by simpa using hj)
      obtain ⟨e, h1, h2⟩ := GlobalTheory.T.exists_levelOne_form_one_add_expDecay (w j₀ - w j + 4) (by omega)
        (((hF j₀).1.sub_odd (hF j).1).add (by decide))
      refine ⟨c j • e, h1.smul _, (h2.const_mul_left (c j)).congr_left fun τ => ?_⟩
      simp [mul_sub]
  choose e heMF heO using he
  have hH : IsMF Γ (w j₀ + 4) (∑ j, e j * F j) :=
    IsMF.sum _ fun j _ => ((heMF j).mono le_top).mul (hF j).2 (by ring)
  have hHx : ∀ x : SL(2, ℤ), (∑ j, e j * F j) ∣[w j₀ + 4] x = ∑ j, e j * (F j ∣[w j] x) := by
    intro x
    rw [slash_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : w j₀ + 4 = (w j₀ - w j + 4) + w j := by ring
    rw [this, ModularForm.mul_slash_SL2, (heMF j).slash_top]
  have hHO : ∀ x : SL(2, ℤ), ((∑ j, e j * F j) ∣[w j₀ + 4] x) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 : (fun τ : ℍ => ∑ j, (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
        fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      have h2 : ∀ j, (fun τ : ℍ => (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
          fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
        intro j
        have hb' : (F j ∣[w j] x) =O[atImInfty] (fun _ => (1 : ℝ)) := (hF j).2.2.2 x
        simpa only [mul_one] using (heO j).mul hb'
      exact (IsBigO.sum (s := Finset.univ) fun j _ => h2 j).congr_left fun τ => Finset.sum_apply _ _ _
    rw [hHx]
    refine (h1.add (hO x)).congr_left fun τ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by simp; ring
  obtain ⟨G, hG, hHG⟩ := GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps Γ _ _ hH hHO
  have hΔ : IsMF ⊤ 12 ModularForm.discriminant := (isCF_coe_top CuspForm.discriminant).isMF
  refine ⟨j₀, w j₀ + 4 - 12, G, ModularForm.discriminant, e, by omega, ?_, hG,
    fun j => (heMF j).2.1, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := (hF j₀).1
    exact ⟨m - 4, by omega⟩
  · intro h0
    have h1 := (heO j₀).trans_tendsto tendsto_exp_neg_im
    rw [h0] at h1
    simp only [Pi.zero_apply, zero_sub] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    exact hc₀ (neg_eq_zero.mp this.symm)
  · intro x τ
    have h1 := hHx x
    have h2 : w j₀ + 4 = 12 + (w j₀ + 4 - 12) := by ring
    rw [hHG, h2, ModularForm.mul_slash_SL2, hΔ.slash_top] at h1
    have h3 := congrFun h1 τ
    simpa [Finset.sum_apply] using h3

end GlobalTheory.OddFrame
end

section

noncomputable section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_inv_qParam_pow_mul {M a : ℕ} (ha : a < M) {g : ℍ → ℂ}
    (hg : g =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    Tendsto (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹ * g τ) atImInfty (𝓝 0) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_le a).trans_lt ha
  have haM : (a : ℝ) < M := by exact_mod_cast ha
  have h1 : (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹) =O[atImInfty]
      fun τ : ℍ => Real.exp (2 * Real.pi * τ.im * a / M) := by
    refine Asymptotics.IsBigO.of_norm_le fun τ => le_of_eq ?_
    rw [norm_inv, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, ← Real.exp_neg, coe_im]
    congr 1; ring
  refine (h1.mul hg).trans_tendsto ?_
  have hr : -2 * Real.pi * (1 - a / M) < 0 := by
    have : (a : ℝ) / M < 1 := (div_lt_one hM).2 haM
    have := Real.pi_pos
    nlinarith
  have h2 : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  refine (Real.tendsto_exp_atBot.comp (h2.const_mul_atTop_of_neg hr)).congr fun τ => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_add]; congr 1; ring

theorem sum_mul_co_eq {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} {w : Fin r → ℤ}
    {F : Fin r → ℍ → ℂ} (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (l : Fin r) {a : ℕ} (ha : a < M) (c : Fin r → ℂ)
    (hc : ∀ i, (leadM M s w F).mulVec c i = co M (w l) (F l) (s i) a) (x : SL(2, ℤ)) {n : ℕ} (hn : n < M) :
    ∑ j, c j * co M (w j) (F j) x n = if n = a then co M (w l) (F l) x a else 0 := by
  have H := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  rw [← sub_eq_zero]
  refine GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero M Γ r s
    (fun x n => ∑ j, c j * co M (w j) (F j) x n - if n = a then co M (w l) (F l) x a else 0)
    hM hs ?_ ?_ ?_ ?_ x n hn
  · intro x n
    simp only [fun j => (H j).1, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · split_ifs with h
      · rw [h]
      · simp
  · intro γ hγ x n
    simp only [fun j => (H j).2.1 γ hγ]
  · intro x n
    simp only [fun j => (H j).2.2 (hF j).1, mul_neg, Finset.sum_neg_distrib]
    split_ifs <;> ring
  · intro i
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range M) a, if_pos (Finset.mem_range.2 ha),
      ← hc i, Finset.sum_comm, sub_eq_zero]
    simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, mul_comm]

theorem exists_tendsto_evM_mul (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (leadM M s w F).det ≠ 0) :
    ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ,
      Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧
        Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  set c : Fin r → ℕ → Fin r → ℂ := fun l a =>
    (leadM M s w F)⁻¹.mulVec fun i => co M (w l) (F l) (s i) a with hcdef
  have hc : ∀ l a i, (leadM M s w F).mulVec (c l a) i = co M (w l) (F l) (s i) a := by
    intro l a i
    simp only [hcdef]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  set t : ℍ → ℂ := fun τ => Function.Periodic.qParam (M : ℝ) (τ : ℂ) with ht
  have ht0 : ∀ τ, t τ ≠ 0 := fun τ => Complex.exp_ne_zero _
  refine ⟨fun τ => Matrix.of fun j l => ∑ a ∈ Finset.range M, c l a j * (t τ ^ a)⁻¹, ?_, ?_⟩
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun l => ?_
    have hlim : Tendsto (fun τ : ℍ => leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j *
        ((t τ ^ a)⁻¹ * ((F j ∣[w j] s i) τ -
          ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n))) atImInfty
        (𝓝 (leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j * 0)) := by
      refine tendsto_const_nhds.add (tendsto_finsetSum _ fun a ha => tendsto_finsetSum _ fun j _ => ?_)
      exact (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha)
        (GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 (s i))).const_mul _
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.mul_apply, evM, leadM, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    have key : ∑ j, c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n =
        co M (w l) (F l) (s i) a * t τ ^ a := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ n ∈ Finset.range M, ∑ j, c l a j * (co M (w j) (F j) (s i) n * t τ ^ n) =
          if n = a then co M (w l) (F l) (s i) a * t τ ^ a else 0 := by
        intro n hn
        simp only [← mul_assoc, ← Finset.sum_mul]
        rw [sum_mul_co_eq hM hΓ hs hF l ha' (c l a) (hc l a) (s i) (Finset.mem_range.1 hn)]
        split_ifs with h
        · rw [h]
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range M) a, if_pos ha]
    have hta : t τ ^ a ≠ 0 := pow_ne_zero _ (ht0 τ)
    have e : co M (w l) (F l) (s i) a =
        ∑ j, (t τ ^ a)⁻¹ * (c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n) := by
      rw [← Finset.mul_sum, key]; field_simp
    rw [e, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun l => ?_
    have hΔ : ModularForm.discriminant =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      simpa [CuspForm.coe_discriminant] using
        CuspFormClass.exp_decay_atImInfty CuspForm.discriminant one_pos one_mem_strictPeriods_SL
    have hlim : Tendsto (fun τ : ℍ => ∑ a ∈ Finset.range M, c l a j *
        ((t τ ^ a)⁻¹ * ModularForm.discriminant τ)) atImInfty (𝓝 (∑ a ∈ Finset.range M, c l a j * 0)) :=
      tendsto_finsetSum _ fun a ha =>
        (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha) hΔ).const_mul _
    simp only [mul_zero, Finset.sum_const_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.OddFrame
end
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.exists_derivationModIntegral_extension_p_cube : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt (p := p) (D b - (p : Ω) ^ 3 * d b) := by
  first | exact @GlobalTheory.DerExt.exists_ext | exact GlobalTheory.DerExt.exists_ext | (intros; apply GlobalTheory.DerExt.exists_ext <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.exists_dlog_derivations_glued_tower_levels : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
  (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
  ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  first | exact @GlobalTheory.LevGlue.glue | exact GlobalTheory.LevGlue.glue | (intros; apply GlobalTheory.LevGlue.glue <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.towerGaloisFixed_eq_div_levelElements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
  ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  first | exact @GlobalTheory.FixFrac.fixed_eq_div | exact GlobalTheory.FixFrac.fixed_eq_div | (intros; apply GlobalTheory.FixFrac.fixed_eq_div <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt (p := p) (D (tr (u l * (x * v k))))) → IsInt (p := p) ((p : Ω) ^ 2 * D x) := by
  first | exact @GlobalTheory.KumDlog.der_dual_p_sq_int | exact GlobalTheory.KumDlog.der_dual_p_sq_int | (intros; apply GlobalTheory.KumDlog.der_dual_p_sq_int <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.kaehler_relation_derivationModIntegral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω), (∀ x ∈ S, IsInt (p := p) x) → (∀ x, ι x ∈ S) →
  ∀ D : Ω → Ω, IsDer S D → ∀ a b c x y z : On p n,
  a • KaehlerDifferential.D (O0 p) (On p n) x = b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z →
  IsInt (p := p) (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  first | exact @GlobalTheory.KumDlog.kaehler_rel_isInt | exact GlobalTheory.KumDlog.kaehler_rel_isInt | (intros; apply GlobalTheory.KumDlog.kaehler_rel_isInt <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  first | exact @GlobalTheory.traceTower_dualData | exact GlobalTheory.traceTower_dualData | (intros; apply GlobalTheory.traceTower_dualData <;> assumption)
end
