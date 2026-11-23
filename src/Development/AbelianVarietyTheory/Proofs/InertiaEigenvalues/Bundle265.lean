module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle239
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle238
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.PAdicHodge.TiltField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle244
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_kernel_le_six_mul :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ J : Subgroup (L ≃ₐ[F] L), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ jumpSum (wild F L) ⊤ J ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r x a hp hE hord hax hx hne
  have hadd : ∀ σ τ : L ≃ₐ[F] L, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := fun σ τ =>
    GlobalTheory.T.integer_coboundary_additive_mod_prime_pow F L p E r ⊤ x a hp hE hord (fun σ _ => hx σ) σ (Subgroup.mem_top _) τ (Subgroup.mem_top _)
  obtain ⟨J, hJn, σ₁, c, hJ, hc, hpc⟩ := GlobalTheory.T.character_mod_prime_pow_kernel_generator (L ≃ₐ[F] L) p r a hp hadd hne
  refine ⟨J, hJ, ?_⟩

  have hp0 : (p : L) ≠ 0 := by
    intro h0
    have h1 : ((p : 𝒪[L]) : L) = 0 := by simpa using h0
    have h2 : (p : 𝒪[L]) = 0 := Subtype.ext (by simpa using h1)
    unfold OrdIs at hord
    rw [h2, AddValuation.map_zero] at hord
    exact ENat.top_ne_coe E hord
  set M := IntermediateField.fixedField J with hM
  haveI : IsGalois F M := IsGalois.of_fixedField_normal_subgroup J
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_integer_fixedField_trace_eq_sq_mul_of_ax F L p r x a J σ₁ c hp0 hax hx (fun σ hσ => (hJ σ).1 hσ) hc
  obtain ⟨e, hordF, hEe, -⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hEe; omega
    · exact h

  change E = ramificationIndex F L * e at hEe
  have hdM : differentExponent F M < ramificationIndex F M * (3 * e) := by
    by_contra hle
    push_neg at hle
    obtain ⟨w, hw, hwt⟩ := GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent F M (3 * e) hle z
    exact GlobalTheory.T.sq_mul_not_mem_maximalIdeal_pow_three_mul F p e c hp he hordF hpc w hw (hwt.trans hz)
  have htow := differentExponent_tower F M L
  change differentExponent F L = ramificationIndex M L * differentExponent F M + differentExponent M L at htow
  have hram := ramificationIndex_tower F M L
  have hjs : jumpSum (wild F L) ⊤ J + 2 * differentExponent M L ≤ 2 * differentExponent F L := GlobalTheory.T.ramificationJumpSum_add_two_mul_differentExponent_le F L J
  have key : jumpSum (wild F L) ⊤ J ≤ 2 * (ramificationIndex M L * differentExponent F M) := by omega
  have hML : ramificationIndex M L * differentExponent F M ≤ ramificationIndex M L * (ramificationIndex F M * (3 * e)) :=
    Nat.mul_le_mul_left _ hdM.le
  have : ramificationIndex M L * (ramificationIndex F M * (3 * e)) * 2 = 6 * E := by
    rw [hEe, hram]; ring
  nlinarith

end GlobalTheory.PMon.Ram
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PSer

theorem emod_toNat_lt (h : ℕ) (hh : 1 ≤ h) (k : ℤ) : (k % (h : ℤ)).toNat < h := by
  have h0 : (0 : ℤ) < h := by exact_mod_cast hh
  have := Int.emod_lt_of_pos k h0
  have := Int.emod_nonneg k h0.ne'
  omega

def reCoef (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) : ℂ_[l] :=
  (l : ℂ_[l]) ^ (-(k / (h : ℤ))) * μ ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩

theorem reCoef_add (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) :
    reCoef l h hh μ k = (l : ℂ_[l]) * reCoef l h hh μ (k + h) := by
  have hl : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have e1 : (k + h) / (h : ℤ) = k / h + 1 := by
    have := Int.add_mul_ediv_right k 1 h0; simpa using this
  have e2 : (k + h) % (h : ℤ) = k % h := by simp
  unfold reCoef
  simp only [e1, e2]
  rw [neg_add, zpow_add₀ hl, zpow_neg_one]
  field_simp

theorem reCoef_at (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (n : ℤ) (i : Fin h) :
    reCoef l h hh μ (n * h + i) = (l : ℂ_[l]) ^ (-n) * μ i := by
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  have hih : (i : ℤ) < h := by exact_mod_cast i.isLt
  have e1 : (n * h + i) / (h : ℤ) = n := by
    rw [add_comm, Int.add_mul_ediv_right _ _ h0, Int.ediv_eq_zero_of_lt hi0 hih, zero_add]
  have e2 : (n * h + i) % (h : ℤ) = i := by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]
  unfold reCoef
  congr 2
  · rw [e1]
  · ext; simp [e2]

theorem emod_at (h : ℕ) (hh : 1 ≤ h) (n : ℤ) (i : Fin h) :
    (n * h + ((i : ℕ) : ℤ)) % (h : ℤ) = ((i : ℕ) : ℤ) := by
  have hi0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
  have hih : ((i : ℕ) : ℤ) < h := by exact_mod_cast i.isLt
  rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]

theorem exists_coef_hasSum_lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 →
    ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧
      ∀ x : Fl l, ‖sh x‖ < 1 →
        HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  intro l _ h μ hh hμ
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  refine ⟨reCoef l h hh μ, reCoef_add l h hh μ, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra H; push_neg at H; exact hμ (funext H)
    refine ⟨((i : ℕ) : ℤ), ?_⟩
    have := reCoef_at l h hh μ 0 i
    simp only [zero_mul, zero_add, neg_zero, zpow_zero, one_mul] at this
    rw [this]; exact hi
  · intro x hx
    let f : ℤ → ℂ_[l] := fun k => reCoef l h hh μ k * sh (pw k x)
    let F : Fin h → ℤ → ℂ_[l] := fun i k => if k % (h : ℤ) = ((i : ℕ) : ℤ) then f k else 0
    have hF : ∀ k, f k = ∑ i, F i k := by
      intro k
      have hn : 0 ≤ k % (h : ℤ) := Int.emod_nonneg k h0
      rw [Finset.sum_eq_single ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩]
      · simp only [F]; rw [if_pos (by simp [Int.toNat_of_nonneg hn])]
      · intro b _ hb
        simp only [F]
        rw [if_neg]
        intro hbk
        apply hb
        ext
        simp only
        omega
      · intro hc; exact absurd (Finset.mem_univ _) hc
    have hFi : ∀ i : Fin h, HasSum (F i) (μ i * lam h i x) := by
      intro i
      have hg : Function.Injective (fun n : ℤ => n * h + ((i : ℕ) : ℤ)) := by
        intro a b e
        have e' : a * (h : ℤ) = b * h := by simpa using e
        exact mul_right_cancel₀ h0 e'
      rw [← hg.hasSum_iff]
      · have := ((GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h i ‖sh x‖ x hh hx le_rfl).1).mul_left (μ i)
        have heq : (F i ∘ fun n : ℤ => n * h + ((i : ℕ) : ℤ)) =
            fun n : ℤ => μ i * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((i : ℕ) : ℤ)) x)) := by
          funext n
          simp only [Function.comp, F, f]
          rw [if_pos (emod_at h hh n i), reCoef_at]
          ring
        rw [heq]; exact this
      · intro k hk
        simp only [F]
        rw [if_neg]
        intro hki
        apply hk
        refine ⟨k / h, ?_⟩
        have := Int.ediv_mul_add_emod k (h : ℤ)
        simp only
        rw [← hki]
        linarith [mul_comm (k / (h : ℤ)) (h : ℤ)]
    have := hasSum_sum (s := Finset.univ) (fun i _ => hFi i)
    have hf : f = fun k => ∑ i, F i k := funext hF
    show HasSum f _
    rw [hf]; exact this

end GlobalTheory.PSer
end
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧ ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  first | exact @GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le | exact GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le | (intros; apply GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.sum_mul_untiltFrobeniusDoubleSeries_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (i : ℕ) (y : ℕ → Fin h → Fl l) (ρ : ℝ),
    1 ≤ h → ρ < 1 → (∀ k j, ‖sh (y k j)‖ ≤ ρ) →
    HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j)) 0 →
    ∑ j, μ j * abelian₂ h i (fun k => y k j) = 0 := by
  first | exact @GlobalTheory.PSer.sum_mul_Lam_eq_zero | exact GlobalTheory.PSer.sum_mul_Lam_eq_zero | (intros; apply GlobalTheory.PSer.sum_mul_Lam_eq_zero <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  first | exact @GlobalTheory.gam_laws | exact GlobalTheory.gam_laws | (intros; apply GlobalTheory.gam_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ → ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | exact GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | (intros; apply GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ), lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B → (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | exact GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | (intros; apply GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

theorem tilt_isAlgClosed_and_unitBall : ∀ (l : ℕ) [Fact l.Prime],
    IsAlgClosed (FractionRing (PreTilt (normInteger ℂ_[l]) l)) ∧
      ∃ ι : Fl l →+* FractionRing (PreTilt (normInteger ℂ_[l]) l),
        (∀ x, tiltSharp (K := ℂ_[l]) (p := l) (ι x) = sh x) ∧
        (∀ z : FractionRing (PreTilt (normInteger ℂ_[l]) l), ‖z‖ ≤ 1 → ∃ x, ι x = z) := by
  intro l _
  obtain ⟨e, he⟩ := exists_flEquiv_untilt l
  have hC : IsAlgClosed (Formalism.BasicNotions.Loc.Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  refine ⟨?_, (algebraMap (PreTilt (normInteger ℂ_[l]) l) _).comp (e : Fl l →+* _), ?_, ?_⟩
  · let e' : Formalism.BasicNotions.Loc.Cb l ≃+* FractionRing (PreTilt (normInteger ℂ_[l]) l) :=
      IsFractionRing.ringEquivOfRingEquiv (A := Formalism.BasicNotions.Loc.OCb l) (B := PreTilt (normInteger ℂ_[l]) l) e
    exact IsAlgClosed.of_ringEquiv _ _ e'
  · intro x
    rw [RingHom.comp_apply, tiltSharp_algebraMap]
    exact he x
  · intro z hz
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz
    exact ⟨e.symm a, by simp⟩

end GlobalTheory.PSer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.axLemma_finiteGalois_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  first | exact @GlobalTheory.PMon.Ram.axIn_padic | exact GlobalTheory.PMon.Ram.axIn_padic | (intros; apply GlobalTheory.PMon.Ram.axIn_padic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l)) (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ), (∀ i, x i ∈ Set.range (algebraMap L (Om l))) → (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) → (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') → Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  first | exact @GlobalTheory.PMon.Ram.detects_restrictNormal_inf | exact GlobalTheory.PMon.Ram.detects_restrictNormal_inf | (intros; apply GlobalTheory.PMon.Ram.detects_restrictNormal_inf <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

theorem _root_.GlobalTheory.T.twisted_dual_families_continuous : StepCont := by
  first | exact @GlobalTheory.Pass.FamCont.stepCont | exact GlobalTheory.Pass.FamCont.stepCont | (intros; apply GlobalTheory.Pass.FamCont.stepCont <;> assumption)
end

section

noncomputable section

open scoped Formalism.Per
open Filter Topology

namespace GlobalTheory.PMon.Gauss

theorem abs_sub_le_of_le_max {a b t : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ max b t) (hba : b ≤ max a t) :
    |a - b| ≤ t := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.2 h)]
    rcases le_max_iff.1 hba with h' | h'
    · linarith
    · linarith
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    rcases le_max_iff.1 hab with h' | h'
    · linarith
    · linarith

variable {l : ℕ} [Fact l.Prime]

theorem isGauss_natCast {ρ : ℝ} (hρ : 0 ≤ ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N) :
    N (l : Formalism.Per.Acris l) = ρ := by
  rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, hN.2.2.2.2]
  exact GlobalTheory.GaussSlope.gauss_l l hρ

theorem isGauss_pow_mul {ρ : ℝ} (hρ : 0 ≤ ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    (k : ℕ) (x : Formalism.Per.Acris l) : N ((l : Formalism.Per.Acris l) ^ k * x) = ρ ^ k * N x := by
  rw [GlobalTheory.GaussSlope.map_pow_mul N hN.2.2.2.1, isGauss_natCast hρ hN]

theorem isGauss_eq_on_acris0 {ρ : ℝ} (hρ : 0 < ρ) {N N' : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    (hN' : IsGauss l ρ N') (s : Formalism.Per.Acris0 l) :
    N (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) =
      N' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) := by
  obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
  have h1 := congrArg N ha
  have h2 := congrArg N' ha
  rw [isGauss_pow_mul hρ.le hN, hN.2.2.2.2] at h1
  rw [isGauss_pow_mul hρ.le hN', hN'.2.2.2.2] at h2
  have hk : ρ ^ k ≠ 0 := pow_ne_zero _ hρ.ne'
  exact mul_left_cancel₀ hk (h1.trans h2.symm)

theorem isGauss_abs_sub_le {ρ : ℝ} (hρ : 0 ≤ ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    (s z : Formalism.Per.Acris l) (r : ℕ) : |N (s + (l : Formalism.Per.Acris l) ^ r * z) - N s| ≤ ρ ^ r := by
  obtain ⟨h01, hadd, hneg, -, -⟩ := id hN
  have hz : N ((l : Formalism.Per.Acris l) ^ r * z) ≤ ρ ^ r := by
    rw [isGauss_pow_mul hρ hN]
    exact mul_le_of_le_one_right (pow_nonneg hρ _) (h01 z).2
  apply abs_sub_le_of_le_max (pow_nonneg hρ _) (h01 _).1 (h01 _).1
  · exact (hadd _ _).trans (max_le_max le_rfl hz)
  · have := hadd (s + (l : Formalism.Per.Acris l) ^ r * z) (-((l : Formalism.Per.Acris l) ^ r * z))
    rw [add_neg_cancel_right, hneg] at this
    exact this.trans (max_le_max le_rfl hz)

theorem isGauss_unique : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ) (N N' : Formalism.Per.Acris l → ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 →
    IsGauss l ρ N → IsGauss l ρ N' → N = N' := by
  intro l _ ρ N N' hρl hρ1 hN hN'
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ : 0 < ρ := (inv_pos.2 hl).trans_le hρl
  funext x
  have hb : ∀ r : ℕ, |N x - N' x| ≤ 2 * ρ ^ r := by
    intro r
    obtain ⟨s, z, hx⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    have e := isGauss_eq_on_acris0 hρ hN hN' s
    have h1 := isGauss_abs_sub_le hρ.le hN (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) z r
    have h2 := isGauss_abs_sub_le hρ.le hN' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) z r
    rw [← hx] at h1 h2
    rw [e] at h1
    calc |N x - N' x| = |(N x - N' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s)) -
          (N' x - N' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s))| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ 2 * ρ ^ r := by linarith
  have ht : Tendsto (fun r : ℕ => 2 * ρ ^ r) atTop (𝓝 (2 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul 2
  rw [mul_zero] at ht
  have h0 : |N x - N' x| ≤ 0 := ge_of_tendsto' ht hb
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

end GlobalTheory.PMon.Gauss

end
end
