module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeDeltaInvariantBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystalline
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneReductionFrobeniusPullbackEqShift
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle439
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachLattice_deltaInvariant_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.s = 1 → l ≠ 2 → ∀ (e s' : ℕ) (π' : AA K LL) (E' : Let K → Polynomial ↥(OL LL)), 0 < s' → wachRingRelations W e s' π' E' → wachModuleOverLetters W T π' := by
  first | exact @GlobalTheory.NL.InvBasis.invariant_basis | exact GlobalTheory.NL.InvBasis.invariant_basis | (intros; apply GlobalTheory.NL.InvBasis.invariant_basis <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, Module.Free ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) ∧ Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) := by
  first | exact @GlobalTheory.NL.QuoFree.quo_free_finite | exact GlobalTheory.NL.QuoFree.quo_free_finite | (intros; apply GlobalTheory.NL.QuoFree.quo_free_finite <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem untilt_zero' : (0 : Formalism.Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem isGauss_gC {ρ : ℝ} (h1 : (l : ℝ)⁻¹ ≤ ρ) (h2 : ρ < 1) : IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := by
    obtain ⟨N, hN⟩ := GlobalTheory.GaussExt.exists_gauss_acris l ρ h1 h2
    exact ⟨N, hN⟩
  have hfun : gC l ρ = Classical.choose h := by
    funext x
    unfold gC
    rw [dite_eq_left h]
  rw [hfun]
  exact Classical.choose_spec h

theorem gC_sub_le {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (x y : Formalism.Per.Acris l) :
    gC l ρ (x - y) ≤ max (gC l ρ x) (gC l ρ y) := by
  rw [sub_eq_add_neg]
  calc _ ≤ max (gC l ρ x) (gC l ρ (-y)) := hG.2.1 _ _
    _ = _ := by rw [hG.2.2.1]

theorem gC_pow {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (h1 : gC l ρ 1 = 1) (x : Formalism.Per.Acris l) (n : ℕ) :
    gC l ρ (x ^ n) = gC l ρ x ^ n := by
  induction n with
  | zero => simp [h1]
  | succ n ih => rw [pow_succ, hG.2.2.2.1, ih, pow_succ]

theorem gA_le_of_coeff_zero {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l)
    (ha : a.coeff 0 = 0) : gA l ρ a ≤ ρ := by
  unfold gA
  apply ciSup_le
  intro n
  rcases n with _ | n
  · simpa [ha, untilt_zero'] using h0
  · have hn : ‖(((a.coeff (n + 1)).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ (n + 1)) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _) (by positivity)
    calc _ ≤ 1 * ρ ^ (n + 1) := mul_le_mul_of_nonneg_right hn (pow_nonneg h0 _)
      _ ≤ ρ := by rw [one_mul]; exact pow_le_of_le_one h0 h1 (Nat.succ_ne_zero n)

theorem tc_mul (a b : Formalism.Per.Fl l) : tc l (a * b) = tc l a * tc l b := by
  unfold tc
  rw [Formalism.Per.tm, map_mul, map_mul]

end GlobalTheory.GaussCancel

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem equal_gauss_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 →
    (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧
      gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  intro l _ w w' hw' heq
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  obtain ⟨⟨c, k, ρ₂, hc, hρ₂, hρ₂1, hm'⟩, -⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l w' hw' (l : ℝ)⁻¹ le_rfl hlinv
  have hm : ∀ ρ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂, gC l ρ w = c * ρ ^ k := fun ρ hρ => by
    rw [heq ρ hρ.1 (lt_of_le_of_lt hρ.2 hρ₂1)]; exact hm' ρ hρ
  obtain ⟨y', j', hkj', hy', hL'⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w' c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm'
  obtain ⟨y, j, hkj, hy, hL⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm

  have hy'0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy'
    linarith
  have hdvd : y' ∣ y := by
    apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
    have hq : ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
      rw [GlobalTheory.RingBasics.mem_OC, norm_div, hy, hy', div_self hc.ne']
    refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
    change ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) *
      (((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]))
    field_simp
  obtain ⟨u, hu⟩ := hdvd
  have hu1 : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((1 : Formalism.Per.Fl l).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
    have h := hy
    rw [hu, map_mul] at h
    push_cast at h
    rw [norm_mul, hy'] at h
    rw [map_one]
    simp only [OneMemClass.coe_one, norm_one]
    have : c * ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hc.ne' this
  obtain ⟨ζ, o, ho, hζ, hζ0, hlt⟩ := GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio l u 1 one_ne_zero hu1
  rw [mul_one, map_one] at hlt
  simp only [OneMemClass.coe_one, norm_one] at hlt

  set ρ₀ : ℝ := ((l : ℝ)⁻¹ + ρ₂) / 2 with hρ₀def
  have hρ₀a : (l : ℝ)⁻¹ < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀b : ρ₀ < ρ₂ := by rw [hρ₀def]; linarith
  have hρ₀1 : ρ₀ < 1 := lt_trans hρ₀b hρ₂1
  have hρ₀pos : 0 < ρ₀ := lt_trans hlpos hρ₀a
  have hIoo : ρ₀ ∈ Set.Ioo (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a, hρ₀b⟩
  have hIcc : ρ₀ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a.le, hρ₀b.le⟩
  refine ⟨ζ, o, ρ₀, ho, hζ, hζ0, hρ₀a, hρ₀1, ?_⟩
  have hG := isGauss_gC (l := l) hρ₀a.le hρ₀1
  obtain ⟨hb1, hbl, -, hbt, -⟩ := GlobalTheory.T.gaussNormAcris_basic_values l ρ₀ hρ₀a.le hρ₀1
  have hlpow : ∀ n : ℕ, gC l ρ₀ ((l : Formalism.Per.Acris l) ^ n) = ρ₀ ^ n := fun n => by
    rw [gC_pow hG hb1, hbl]
  have hGw' : gC l ρ₀ w' = c * ρ₀ ^ k := hm' ρ₀ hIcc
  have hGw : gC l ρ₀ w = c * ρ₀ ^ k := hm ρ₀ hIcc
  set T : ℝ := ρ₀ ^ (max j j') * (c * ρ₀ ^ k) with hTdef
  set J : ℕ := max j j' with hJ
  set m : ℕ := (k + J).toNat with hmdef

  have hA : ∀ (x : Formalism.Per.Acris l) (z : Formalism.Per.Fl l) (i : ℕ), 0 ≤ k + i → i ≤ J → gC l ρ₀ x = c * ρ₀ ^ k →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ i * x - (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) < ρ₀ ^ i * gC l ρ₀ x →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z) < T := by
    intro x z i hki hiJ hx hlt'
    have hmi : m = (J - i) + (k + i).toNat := by rw [hmdef]; omega
    have heqA : (l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z =
        (l : Formalism.Per.Acris l) ^ (J - i) * ((l : Formalism.Per.Acris l) ^ i * x -
          (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) := by
      have e : (l : Formalism.Per.Acris l) ^ J = (l : Formalism.Per.Acris l) ^ (J - i) * (l : Formalism.Per.Acris l) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiJ]
      rw [hmi, e, pow_add]
      ring
    rw [heqA, hG.2.2.2.1, hlpow, hTdef, ← hx]
    calc ρ₀ ^ (J - i) * gC l ρ₀ _ < ρ₀ ^ (J - i) * (ρ₀ ^ i * gC l ρ₀ x) :=
          mul_lt_mul_of_pos_left hlt' (pow_pos hρ₀pos _)
      _ = ρ₀ ^ J * gC l ρ₀ x := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hiJ]
  have hAw := hA w y j hkj (le_max_left _ _) hGw (hL ρ₀ hIoo)
  have hAw' := hA w' y' j' hkj' (le_max_right _ _) hGw' (hL' ρ₀ hIoo)

  have hζ1 : gC l ρ₀ (tc l ζ) ≤ 1 := (hG.1 _).2
  have hdiff : gC l ρ₀ (tc l u - tc l ζ) < 1 := by
    have hsplit : tc l u - tc l ζ = tc l (u - ζ) + algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)
        (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) := by
      unfold tc
      rw [map_sub, map_sub]
      ring
    have hc0 : (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)).coeff 0 = 0 := by
      change WittVector.constantCoeff (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) = 0
      rw [map_sub, map_sub]
      change (Formalism.Per.tm u).coeff 0 - (Formalism.Per.tm ζ).coeff 0 - (Formalism.Per.tm (u - ζ)).coeff 0 = 0
      simp [Formalism.Per.tm, WittVector.teichmuller_coeff_zero]
    rw [hsplit]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt ?_ ?_)
    · rw [hbt]; exact hlt
    · rw [hG.2.2.2.2]
      exact lt_of_le_of_lt (gA_le_of_coeff_zero hρ₀pos.le hρ₀1.le _ hc0) hρ₀1
  have hmz : ((m : ℕ) : ℤ) = k + J := by rw [hmdef]; exact Int.toNat_of_nonneg (by omega)
  have hD : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y')) < T := by
    have : tc l y - tc l ζ * tc l y' = tc l y' * (tc l u - tc l ζ) := by
      rw [hu, tc_mul]; ring
    rw [this, hG.2.2.2.1, hG.2.2.2.1, hlpow, hbt, hy']
    have hT : ρ₀ ^ m * c = T := by
      rw [hTdef, ← zpow_natCast, hmz, zpow_add₀ hρ₀pos.ne', zpow_natCast]
      ring
    rw [← hT, ← mul_assoc]
    exact mul_lt_of_lt_one_right (mul_pos (pow_pos hρ₀pos _) hc) hdiff
  have hB : gC l ρ₀ (tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y')) < T := by
    rw [hG.2.2.2.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (hG.1 _).1 hζ1) hAw'
  have hid : (l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w') =
      ((l : Formalism.Per.Acris l) ^ J * w - (l : Formalism.Per.Acris l) ^ m * tc l y) -
        tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y') +
        (l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y') := by ring
  have hbig : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w')) < T := by
    rw [hid]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt (lt_of_le_of_lt (gC_sub_le hG _ _) (max_lt hAw hB)) ?_)
    exact hD
  rw [hG.2.2.2.1, hlpow, hTdef, ← hGw'] at hbig
  exact lt_of_mul_lt_mul_left hbig (pow_nonneg hρ₀pos.le _)

end GlobalTheory.GaussCancel
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.rankOne_reduction_frobeniusPullback_eq_shift : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ a : ZMod S.n → ℤ, A.m = 1 → (∀ i, U i = {a i}) → ∀ i, pull ((F.D A).φ i) (N (i - 1)) = sh (a i) (N i) := by
  first | exact @GlobalTheory.RankOneReduction.pull_eq_sh | exact GlobalTheory.RankOneReduction.pull_eq_sh | (intros; apply GlobalTheory.RankOneReduction.pull_eq_sh <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon



theorem lt_period_conj_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  intro l _ P AI T s hs x hx hφ h1 h2 hj g
  obtain ⟨-, -, hsh, hinv, -, -, -, htz, tadd, t0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have iter_mul : ∀ (m : ℕ) (a b : P.R.B), P.φB^[m] (a * b) = P.φB^[m] a * P.φB^[m] b := by
    intro m a b
    induction m generalizing a b with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_mul]
  have iter_one : ∀ m : ℕ, P.φB^[m] (1 : P.R.B) = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]
  have iter_act : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] (P.actQ g b) = P.actQ g (P.φB^[m] b) := by
    intro m b
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]
  have ev_mul : ∀ (m : ℕ) (a b : P.R.B), ev P m (a * b) = ev P m a * ev P m b := by
    intro m a b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply]
  obtain ⟨w, hw⟩ : ∃ w : P.R.B, x * w = 1 := ⟨_, hx.mul_val_inv⟩
  set y := P.actQ g x * w with hy
  have hyx : y * x = P.actQ g x := by rw [hy, mul_assoc, mul_comm w x, hw, mul_one]

  have hfix : P.φB^[s] y = y := by
    have e1 : P.φB^[s] x * P.φB^[s] w = 1 := by rw [← iter_mul, hw, iter_one]
    rw [hφ] at e1
    rw [hy, iter_mul, iter_act, hφ, map_mul, map_natCast]
    calc (l : P.R.B) * P.actQ g x * P.φB^[s] w = P.actQ g x * (((l : P.R.B) * x * P.φB^[s] w) * w) := by
          linear_combination (-(l : P.R.B) * P.actQ g x * P.φB^[s] w) * hw
      _ = P.actQ g x * w := by rw [e1, one_mul]

  have key : ∀ (k : ℤ) (e u v z : P.R.BdR), e = tz P k * u → u * v = 1 → u ∈ Fil P 0 → v ∈ Fil P 0 →
      z * e = P.actQdR g e → z ∈ Fil P 0 := by
    intro k e u v z he huv hu hv hz
    have hk : tz P k * tz P (-k) = 1 := by rw [← tadd, add_neg_cancel, t0]
    have hz' : z * e = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * tz P k * P.actQdR g u := by
      rw [hz, he, map_mul, htz]
    have hzz : z = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v := by
      linear_combination (-z + algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v) * hk
        - z * tz P k * tz P (-k) * huv - tz P (-k) * v * z * he + tz P (-k) * v * hz'
    rw [hzz]
    exact Fil_mul_right (Fil_mul_left (q_mem_Fil P _) (Fil_act g hu)) hv
  have hev : ∀ j, ev P j y * ev P j x = P.actQdR g (ev P j x) := by
    intro j
    rw [← ev_mul, hyx, ev_act]
  have hfil : ∀ j < s, ev P j y ∈ Fil P 0 := by
    intro j hjs
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
        have := (hsh 1 (-1) (P.ιB x)).1 h1
        rwa [show (1 : ℤ) + -1 = 0 by norm_num] at this
      have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
        intro h
        apply h2
        exact (hsh 2 (-1) (P.ιB x)).2 (by rw [show (2 : ℤ) + -1 = 1 by norm_num]; exact h)
      obtain ⟨v, hv, huv⟩ := hinv _ hu0 hu1
      refine key 1 (ev P 0 x) _ v _ ?_ huv hu0 hv (hev 0)
      change P.ιB x = tz P 1 * (tz P (-1) * P.ιB x)
      rw [← mul_assoc, ← tadd, show (1 : ℤ) + -1 = 0 by norm_num, t0, one_mul]
    · obtain ⟨e0, e1⟩ := hj j hpos hjs
      obtain ⟨v, hv, huv⟩ := hinv _ e0 e1
      exact key 0 (ev P j x) (ev P j x) v _ (by rw [t0, one_mul]) huv e0 hv (hev j)
  obtain ⟨a, ha, hya⟩ := GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T s hs y hfix hfil
  exact ⟨a, ha, by rw [← hyx, hya]⟩

end GlobalTheory.PMon

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem phiB_moore_det {l : ℕ} [Fact l.Prime] (P : LocPrime l) (n : ℕ) (a : Fin (n + 1) → P.R.B)
    (ha : ∀ j, P.φB^[n + 1] (a j) = (l : P.R.B) * a j) :
    P.φB (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det =
      (-1) ^ n * (l : P.R.B) * (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det := by
  set M := Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j) with hM
  have h1 : P.φB M.det = (M.map P.φB).det := by
    rw [AlgHom.map_det]; rfl
  have h2 : M.map P.φB = Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (l : P.R.B) else 1) *
      M.submatrix (finRotate (n + 1)) id := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.map_apply, Matrix.submatrix_apply, finRotate_apply, id]
    simp only [hM, Matrix.of_apply]
    rw [← Function.iterate_succ_apply' (f := P.φB)]
    by_cases hi : i = Fin.last n
    · subst hi
      simp [ha]
    · rw [if_neg hi, one_mul, Fin.val_add_one, if_neg hi]
  rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, sign_finRotate]
  simp [Finset.prod_ite_eq']
  ring

theorem mooreDeterminant_eq_unramified_mul_period_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) → (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) → (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 → P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1 → ∃ κ : ↥(MaximalUnramifiedExtension l), κ ≠ 0 ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB := by
  intro l _ P AI T h hh a ha _ hd hF
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  set d := (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det with hdd
  have hφd : P.φB d = (-1) ^ n * (l : P.R.B) * d := phiB_moore_det P n a ha
  have ht : IsUnit P.tB := isUnit_tB P
  have hl : IsUnit (l : P.R.B) := by
    have h0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ_[l] P.R.B)
    rwa [map_natCast] at this
  have hφt : P.φB P.tB = (l : P.R.B) * P.tB := by
    rw [localPrime_frobenius_periodT, Algebra.smul_def, map_natCast]
  set c := d * ((ht.unit⁻¹ : P.R.Bˣ) : P.R.B) with hc
  have hct : c * P.tB = d := by
    rw [hc, mul_assoc, Units.inv_mul_of_eq ht.unit_spec, mul_one]
  have hφc : P.φB c = (-1) ^ n * c := by
    apply (hl.mul ht).mul_right_cancel
    have e := congrArg P.φB hct
    rw [map_mul, hφt, hφd, ← hct] at e
    rw [show P.φB c * ((l : P.R.B) * P.tB) = P.φB c * ((l : P.R.B) * P.tB) from rfl]
    linear_combination e
  have hφ2 : P.φB^[2] c = c := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hφc, map_mul, hφc, map_pow, map_neg, map_one, ← mul_assoc,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have hFc : P.ιB c ∈ Fil P 0 := by
    have e : tz P 1 * P.ιB c = P.ιB d := by
      rw [show tz P 1 = P.ιB P.tB by simp [tz], ← map_mul, mul_comm, hct]
    have key := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).2.2.1 0 1 (P.ιB c)
    rw [zero_add, e] at key
    exact key.2 hF
  have hev : ∀ j < 2, ev P j c ∈ Fil P 0 := by
    intro j hj
    interval_cases j
    · simpa [ev] using hFc
    · simp only [ev, Function.iterate_one, hφc, map_mul, map_pow, map_neg, map_one]
      rcases neg_one_pow_eq_or P.R.BdR n with h1 | h1
      · rw [h1, one_mul]; exact hFc
      · rw [h1, neg_one_mul]
        simp only [Fil, SetLike.mem_coe] at hFc ⊢
        exact neg_mem hFc
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T 2 two_pos c hφ2 hev
  refine ⟨κ, ?_, ?_⟩
  · rintro rfl
    apply hd
    rw [← hct, hκ, map_zero, zero_mul]
  · rw [← hκ, hct]

end GlobalTheory.PMon
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_rep_of_frobeniusFixed_frame_change : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w e : Fin r → n → ℤ) (U : Fin r → GL n P.R.BdR) (A : GL n P.R.B), IsRat r ρ → (∀ (m : Fin r) (g : ↥(GK K)), matD P ρ m g * (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])) → (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) → (∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (e m j)) * (W : Matrix n n P.R.BdR)) → ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + e m j) ∧ (AdmSt P ρ' → AdmSt P ρ) := by
  first | exact @GlobalTheory.PMon.exists_rep_of_fixed_frame_change | exact GlobalTheory.PMon.exists_rep_of_fixed_frame_change | (intros; apply GlobalTheory.PMon.exists_rep_of_fixed_frame_change <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem twist_conj {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin k) B) (ρ₀ : Γ →* GL (Fin k) A) (χ₀ : Γ →* Aˣ) (ψ χ : Γ →* Bˣ)
    (hχ : χ = (Units.map (f : A →* B)).comp χ₀ * ψ) (U : GL (Fin k) B)
    (hU : ∀ g, mapRep f ρ₀ g * U = U * ρ g) (g : Γ) :
    twistM ((Units.coeHom _).comp ρ) χ⁻¹ g * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        twistM (mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹)) ψ⁻¹ g := by
  have h1 : ρ g * U⁻¹ = U⁻¹ * mapRep f ρ₀ g := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hU, mul_inv_cancel_right]
  have h2 : ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := congrArg Units.val h1
  have h3 : mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g =
      f (((χ₀ g)⁻¹ : Aˣ) : A) • ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := by
    ext i j
    exact map_mul f _ _
  have h4 : (((χ g)⁻¹ : Bˣ) : B) = (((ψ g)⁻¹ : Bˣ) : B) * f (((χ₀ g)⁻¹ : Aˣ) : A) := by
    rw [hχ, MonoidHom.mul_apply, mul_inv_rev, Units.val_mul, MonoidHom.comp_apply, ← map_inv]
    rfl
  change ((((χ g)⁻¹ : Bˣ) : B) • ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)) * _ =
    _ * ((((ψ g)⁻¹ : Bˣ) : B) • mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g)
  rw [h3, smul_smul, ← h4, Matrix.smul_mul, Matrix.mul_smul, h2]

theorem twistedRho_conj_latTpsi : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π) → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → AbsIrrSub (redRep D.nd a (ρ π)) ⊤ → ∃ U : GL (Fin D.R.r) (D.nd.O a), ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) = (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g := by
  intro hC D a π ρ s Sg hρ hP hT hirr
  have htr := GlobalTheory.T.trace_rankRPart_eq_trace_baseChangeTriple hC D a π (ρ π) s Sg hρ hP hT
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_conj_of_trace_eq_residually_absIrreducible_DVR (D.nd.O a) (Formalism.MainNotions.N.GE D.nd) D.R.r (ρ π)
    (mapRep (D.ntw.twist₂ a) (D.ntw.rhoS _ s)) hirr (fun g => by
      rw [htr g]
      exact (AddMonoidHom.map_trace (D.ntw.twist₂ a) _))
  refine ⟨U⁻¹, fun g => ?_⟩
  refine twist_conj (D.ntw.twist₂ a) (ρ π) (D.ntw.rhoS _ s) _ (D.ntw.psiL a) (D.nd.chi a 1) ?_ U hU g
  rw [hT.1, hT.2.1]
  exact D.ntw.chi_tw a

end GlobalTheory.PtCore
end
