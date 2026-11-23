module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import GroundTheory.LocalFields.ConductorReciprocity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle439
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle441
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachLetterRing_frobenius_decomposition : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  first | exact @GlobalTheory.NL.PhiDec.phi_dec | exact GlobalTheory.NL.PhiDec.phi_dec | (intros; apply GlobalTheory.NL.PhiDec.phi_dec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_theta_deRhamFiltration_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]) (Θ : Formalism.Per.Acris l →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ (∀ a, ‖Θ a‖ ≤ 1) ∧ (∀ z : Formalism.Per.Fl l, Θ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm z)) = sh z) ∧ ∀ a : Formalism.Per.Acris l, ∃ hm, θ ⟨P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)), hm⟩ = Θ a := by
  first | exact @GlobalTheory.PSer.theta_fil_acris | exact GlobalTheory.PSer.theta_fil_acris | (intros; apply GlobalTheory.PSer.theta_fil_acris <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem pw_natCast_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  unfold pw
  rw [zpow_natCast]
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ,
      mul_comm]

theorem two_mul_succ_le_pow (l k h : ℕ) (hl : 2 ≤ l) (hh : 2 ≤ h) :
    2 * (k + 1) ≤ l ^ ((k + 1) * h - 1) := by
  have h1 : 2 * k + 1 < 2 ^ (2 * k + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * k + 1) ≤ l ^ (2 * k + 1) := Nat.pow_le_pow_left hl _
  have h3 : (k + 1) * 2 ≤ (k + 1) * h := Nat.mul_le_mul_left _ hh
  have h4 : l ^ (2 * k + 1) ≤ l ^ ((k + 1) * h - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem terms_mem (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l) (hh : 2 ≤ h)
    (hx : ‖sh x‖ ≤ ‖(l : ℂ_[l])‖) :
    ∃ c : ℤ → Acris l, (∀ n : ℤ, (l : Acris l) ^ n.natAbs ∣ c n) ∧ ∀ n : ℤ,
      (l : Acris l) ^ n.toNat * c n =
        (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
  have key : ∀ n : ℤ, ∃ c : Acris l, (l : Acris l) ^ n.natAbs ∣ c ∧
      (l : Acris l) ^ n.toNat * c =
        (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · cases m with
      | zero => exact ⟨algebraMap (Ainf l) (Acris l) (tm (pw (0 * h) x)), by simp, by simp⟩
      | succ k =>
        have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
        obtain ⟨d, hd⟩ := tm_pow_dvd l x hx
        set y := algebraMap (Ainf l) (Acris l) (tm x)
        set M := l ^ ((k + 1) * h - 1)
        have hM := two_mul_succ_le_pow l k h hl2 hh
        have hN : l ^ ((k + 1) * h) = l * M := by
          have : (k + 1) * h = ((k + 1) * h - 1) + 1 := by
            have : 2 ≤ (k + 1) * h := le_trans hh (Nat.le_mul_of_pos_left h (Nat.succ_pos k))
            omega
          rw [this, pow_succ, mul_comm]
        have hpow : algebraMap (Ainf l) (Acris l) (tm (pw (((k + 1 : ℕ) : ℤ) * h) x)) =
            (l : Acris l) ^ (2 * (k + 1)) * ((l : Acris l) ^ (M - 2 * (k + 1)) * d ^ M) := by
          have e1 : (((k + 1 : ℕ) : ℤ) * (h : ℤ)) = (((k + 1) * h : ℕ) : ℤ) := by push_cast; ring
          rw [e1, pw_natCast_eq_pow, show tm (x ^ l ^ ((k + 1) * h)) = tm x ^ l ^ ((k + 1) * h) from
            map_pow (WittVector.teichmuller l) x _, map_pow, hN, pow_mul, hd, mul_pow, ← mul_assoc,
            ← pow_add, Nat.add_sub_cancel' hM]
        refine ⟨(l : Acris l) ^ (k + 1) * ((l : Acris l) ^ (M - 2 * (k + 1)) * d ^ M), ?_, ?_⟩
        · have e4 : (((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := by omega
          rw [e4]
          exact Dvd.intro _ rfl
        · have e2 : (-((k + 1 : ℕ) : ℤ)).toNat = 0 := by omega
          have e3 : (((k + 1 : ℕ) : ℤ)).toNat = k + 1 := by omega
          rw [e2, e3, pow_zero, one_mul, hpow, ← mul_assoc, ← pow_add]
          ring_nf
    · refine ⟨(l : Acris l) ^ m * algebraMap (Ainf l) (Acris l) (tm (pw (-(m : ℤ) * h) x)),
        ?_, ?_⟩
      · have e4 : (-(m : ℤ)).natAbs = m := by omega
        rw [e4]
        exact Dvd.intro _ rfl
      · have e2 : (-(m : ℤ)).toNat = 0 := by omega
        have e3 : (-(-(m : ℤ))).toNat = m := by omega
        rw [e2, e3, pow_zero, one_mul]
  choose c hc1 hc2 using key
  exact ⟨c, hc1, hc2⟩

end GlobalTheory.PSer
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.TshOnto

theorem tsh_surjective : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ t : ℂ_[l], ∃ z : F, tsh z = t := by
  intro l _ F _ ι tsh _hn hsh _ t
  obtain ⟨-, -, -, -, -, honto, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  by_cases ht : ‖t‖ ≤ 1
  · obtain ⟨x, hx⟩ := honto t ht
    exact ⟨ι x, by rw [hsh, hx]⟩
  · push_neg at ht
    have hinv : ‖t⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ ht.le
    obtain ⟨x, hx⟩ := honto t⁻¹ hinv
    refine ⟨(ι x)⁻¹, ?_⟩
    rw [map_inv₀, hsh, hx, inv_inv]

end GlobalTheory.PSer.TshOnto
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧ (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧ (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧ (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  first | exact @GlobalTheory.PSer.Laws.sh_laws | exact GlobalTheory.PSer.Laws.sh_laws | (intros; apply GlobalTheory.PSer.Laws.sh_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_abelian_nat :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ),
      OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ),
        σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  intro F _ _ _ _ M _ _ p e n h σ hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M n] at hσ
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M
    (min (2 * n) (n + e)), ← map_pow]
  exact Subgroup.mem_map_of_mem _ (GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min F p e n h x hx)

end GlobalTheory.PMon.Ram
end

section

noncomputable section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Trans

variable (l : ℕ) [Fact l.Prime]

theorem map_ne_zero_pt : ∀ y : Formalism.Per.Ainf l, y ≠ 0 →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) y ≠ 0 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  obtain ⟨N, h01, -, -, hmul, hA⟩ := GlobalTheory.GaussExt.exists_gauss_acris l _ le_rfl hr1
  have hbdd : ∀ a : Formalism.Per.Ainf l, BddAbove (Set.range fun n : ℕ =>
      ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n) := by
    intro a
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 :=
      (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
    have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) h1 (by positivity)
    have h3 : ((l : ℝ)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity) hr1.le
    calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpos : ∀ a : Formalism.Per.Ainf l, a ≠ 0 → 0 < N (algebraMap _ _ a) := by
    intro a ha0
    obtain ⟨n, ha⟩ : ∃ n, a.coeff n ≠ 0 := by
      by_contra hc
      apply ha0
      refine WittVector.ext fun n => ?_
      rw [WittVector.zero_coeff]
      by_contra hn
      exact hc ⟨n, hn⟩
    rw [hA]
    refine lt_of_lt_of_le ?_ (le_ciSup (hbdd a) n)
    have hne : (((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
      intro h
      apply ha
      refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l (a.coeff n) 0).2 ?_
      exact Subtype.ext h
    have hl0 : (0 : ℝ) < l := lt_trans one_pos hl
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _) (pow_pos (inv_pos.2 hl0) _)
  have hN0 : N 0 = 0 := by
    have hz : ∀ n : ℕ, (0 : ℝ) ^ ((1 : ℝ) / (l : ℝ) ^ n) = 0 := fun n => Real.zero_rpow (by positivity)
    rw [← map_zero (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)), hA]
    have hz' : ∀ n : ℕ, (0 : ℝ) ^ (((l : ℝ) ^ n)⁻¹) = 0 := fun n => Real.zero_rpow (by positivity)
    simp [hz, hz', GlobalTheory.GaussExt.untilt_zero]
  intro y hy h0
  have := hpos y hy
  rw [h0, hN0] at this
  exact lt_irrefl _ this

theorem tm_sub_one_ne_zero_pt (e : Formalism.Per.Fl l) (he : e ≠ 1) : (Formalism.Per.tm e - 1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  apply he
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) (sub_eq_zero.1 h)
  simpa using h'

theorem one_ne_zero_pt : (1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h
  simp at h'

theorem map_prod_ne_zero_pt : ∀ s : List (Formalism.Per.Fl l), (∀ e ∈ s, e ≠ 1) →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (s.map fun e => Formalism.Per.tm e - 1).prod ≠ 0 := by
  intro s
  induction s with
  | nil =>
    intro _
    rw [List.map_nil, List.prod_nil]
    exact map_ne_zero_pt l 1 (one_ne_zero_pt l)
  | cons e s ih =>
    intro hs
    rw [List.map_cons, List.prod_cons, map_mul]
    intro h
    exact (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).elim
      (map_ne_zero_pt l _ (tm_sub_one_ne_zero_pt l e (hs e List.mem_cons_self)))
      (ih fun e' he' => hs e' (List.mem_cons_of_mem _ he'))

end GlobalTheory.PMon.Trans

theorem GlobalTheory.PMon.Trans.acris_bcris : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)) ∧ (∀ x : Formalism.Per.Acris l, Formalism.Per.φB l (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l x)) ∧ ∀ c : ℤ_[l], algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (zc l c) = Formalism.Per.zB l c := by
  intro l _
  refine ⟨?_, fun x => GlobalTheory.CrisMaps.φB_phiA l x, fun c => (GlobalTheory.RingIface.zB_alg l c).symm⟩
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, h⟩ := GlobalTheory.CrisLoc.exists_pow_mul_eq_zero l e he hne hx
  refine (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).resolve_left ?_
  have h1 := GlobalTheory.PMon.Trans.map_prod_ne_zero_pt l (List.replicate n e)
    fun e' he' => (List.eq_of_mem_replicate he').symm ▸ hne
  rwa [List.map_replicate, List.prod_replicate, map_pow] at h1
end
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem tc_injective (l : ℕ) [Fact l.Prime] : Function.Injective (tc l) := by
  intro a b hab
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  have hinj := GlobalTheory.MemLoc.crisP_injective l j hj
  have key : ∀ y : Formalism.Per.Fl l, j (tc l y) =
      algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l)
        (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.tm y)) := by
    intro y
    have := hj.on0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) (Formalism.Per.tm y))
    rw [Subalgebra.coe_algebraMap, ← GlobalTheory.RingIface.tower] at this
    exact this
  have h1 := congrArg j hab
  rw [key, key] at h1
  have h2 := (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2
    (GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective l h1)
  have h3 := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h2
  simpa using h3

theorem teich_eq_of_phi_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 →
    φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  intro l _ w' ζ hw h
  have hφ : φc l w' ≠ 0 := ((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 w' hw).1
  have hprod : w' * φc l w' ≠ 0 := by
    intro h0
    rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h0 with h0 | h0
    · exact hw h0
    · exact hφ h0
  rw [map_mul, frob_teich] at h
  have h' : (tc l (ζ ^ l) - tc l ζ) * (w' * φc l w') = 0 := by
    linear_combination h
  rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h' with h0 | h0
  · exact tc_injective l (sub_eq_zero.1 h0)
  · exact absurd h0 hprod

end GlobalTheory.PMon.Gauss
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
open Filter Topology

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_lt_one (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  unfold gC
  split_ifs with h
  · have hN := Classical.choose_spec h
    set N := Classical.choose h
    have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
    have hl : N (l : Formalism.Per.Acris l) = ρ := by
      have := hN.2.2.2.2 (l : Formalism.Per.Ainf l)
      rw [map_natCast] at this
      rw [this]
      exact GlobalTheory.GaussSlope.gauss_l l h0
    rw [mul_zero, hl] at hm
    have : (1 - ρ) * N 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · rfl

theorem continuousOn_gC (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) :
    ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  by_cases hx : x = 0
  · subst hx
    refine (continuousOn_const (c := (0 : ℝ))).congr fun ρ hρ => ?_
    exact gC_zero_of_lt_one l (hl0.le.trans hρ.1) hρ.2
  intro ρ₀ hρ₀
  have hpos : 0 < ρ₀ := hl0.trans_le hρ₀.1
  obtain ⟨⟨c, k, ρ₂, -, h02, -, hR⟩, hL⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l x hx ρ₀ hρ₀.1 hρ₀.2
  have hS : Set.Ico (l : ℝ)⁻¹ 1 = (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Iic ρ₀) ∪ (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Ici ρ₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hy
      rcases le_total y ρ₀ with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  rw [ContinuousWithinAt, hS, ← ContinuousWithinAt, continuousWithinAt_union]
  constructor
  · rcases eq_or_lt_of_le hρ₀.1 with heq | hlt
    · refine (continuousWithinAt_singleton (f := fun ρ => gC l ρ x) (x := ρ₀)).mono ?_
      rintro y ⟨hy1, hy2⟩
      exact le_antisymm hy2 (heq ▸ hy1.1)
    · obtain ⟨c', k', ρ₁, -, -, h10, hL'⟩ := hL hlt
      have hg : ContinuousWithinAt (fun ρ : ℝ => c' * ρ ^ k') (Set.Iic ρ₀) ρ₀ :=
        (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k' (Or.inl hpos.ne'))).continuousWithinAt
      have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₁ ρ₀) ρ₀ :=
        (hg.mono Set.Icc_subset_Iic_self).congr (fun y hy => hL' y hy) (hL' ρ₀ ⟨h10.le, le_rfl⟩)
      exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE h10)).mono Set.inter_subset_right
  · have hg : ContinuousWithinAt (fun ρ : ℝ => c * ρ ^ k) (Set.Ici ρ₀) ρ₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k (Or.inl hpos.ne'))).continuousWithinAt
    have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₀ ρ₂) ρ₀ :=
      (hg.mono Set.Icc_subset_Ici_self).congr (fun y hy => hR y hy) (hR ρ₀ ⟨le_rfl, h02.le⟩)
    exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE h02)).mono Set.inter_subset_right

theorem continuousOn_gC_target :
    ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) :=
  fun l _ x => continuousOn_gC l x

end GlobalTheory.PMon.Gauss

end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.integral_of_integral_at_algebraic_points_smooth : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  first | exact @GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points | exact GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points | (intros; apply GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandra_induction_character_restriction_decomp : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∀ (α : Gn g a → ℂ) (β : Gn g b → ℂ), IsChar α → IsChar β → IsChar (hc a b α β n)) ∧ ∀ χ : Gn g n → ℂ, IsChar χ → ∃ L : List ((Gn g a → ℂ) × (Gn g b → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, res a b χ x y = (L.map fun p => p.1 x * p.2 y).sum := by
  first | exact @GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp | exact GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp | (intros; apply GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.classFunction_degree_eq_sum_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ), 0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  first | exact @GlobalTheory.GLq.DegDer.one_eq_sum_der | exact GlobalTheory.GLq.DegDer.one_eq_sum_der | (intros; apply GlobalTheory.GLq.DegDer.one_eq_sum_der <;> assumption)
end
