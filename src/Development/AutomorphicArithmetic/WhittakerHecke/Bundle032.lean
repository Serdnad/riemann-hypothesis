module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.MeasMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle025
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle027
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle029
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle030
import Development.AutomorphicArithmetic.WhittakerHecke.Bundle026
import Development.AutomorphicArithmetic.WhittakerHecke.Bundle023
public import Development.AutomorphicArithmetic.WhittakerHecke.InertOrSplitOfGoodDeltaRat
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem cont_em {E : Type} [Field E] [NumberField E] : Continuous (em E) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)

private theorem ex_rat {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    ∃ γ', em E (gl (ratS ℚ γ)) = ratGL E 2 γ' := by
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap ℚ E) (Matrix.SpecialLinearGroup.toGL γ), ?_⟩
  apply Units.ext
  ext i j
  rw [ratGL_apply]
  exact AdeleBaseChange.adeleMap_algebraMap _

private theorem glm (g h : G1 ℚ) : gl (g * h) = gl g * gl h := map_mul _ _ _

private theorem row_nU (b : A ℚ) (h : GL (Fin 2) (A ℚ)) (j : Fin 2) : (gl (nU b) * h).val 1 j = h.val 1 j := by
  rw [Units.val_mul, M.val_gl]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem row_rat (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (h : GL (Fin 2) (A ℚ)) (j : Fin 2) :
    (gl (ratS ℚ γ) * h).val 1 j = ((fun i => rt (γ.1 1 i)) ᵥ* h.val) j := by
  rw [Units.val_mul, M.val_gl, M.val_ratS]
  rfl

theorem UpperTheory.setIntegral_restrict_mul_thetaKernel_eq_unfolded :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        ∫ g in M₀.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M₀.μ = ∫ p, Un.Tt φ Φ t u p ∂M₀.ν := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨σ, hσ⟩ := G.exists_rowSec (F := ℚ)
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  have hleft : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (h : GL (Fin 2) (A ℚ)), φ (em E (gl (ratS ℚ γ) * h)) = φ (em E h) := by
    intro γ h
    obtain ⟨γ', e⟩ := ex_rat (E := E) γ
    rw [map_mul, e, hA.left]
  have hg : Continuous fun g : G1 ℚ => gl g * dM u := M.continuous_gl.mul continuous_const
  have hm : Measurable (Un.Uu φ Φ t u) := by
    refine Continuous.measurable ?_
    refine (hA.cont.comp (cont_em.comp hg)).mul ((continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j => ?_))
    exact continuous_const.mul ((Units.continuous_val.comp hg).matrix_elem 1 j)
  have hinv : ∀ (ξ : ℚ) g, Un.Uu φ Φ t u (nU (rt ξ) * g) = Un.Uu φ Φ t u g := by
    intro ξ g
    have e : gl (nU (rt ξ) * g) * dM u = gl (nU (rt ξ)) * (gl g * dM u) := by rw [glm, mul_assoc]
    have e' : φ (em E (gl (nU (rt ξ)) * (gl g * dM u))) = φ (em E (gl g * dM u)) := by
      rw [← M.ratS_up]
      exact hleft _ _
    unfold Un.Uu
    rw [e, e']
    simp only [row_nU]
  have key := (M.unfC ℚ M₀ σ (Un.Uu φ Φ t u) hσ hm hinv (UpperTheory.maximalCompact_integral_unipotent_norm_finite E D ω φ hA M₀ Φ hΦ t u hu)).2.2.2
  have e1 : ∀ g, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) = ∑' r, Un.Uu φ Φ t u (ratS ℚ (σ r) * g) := by
    intro g
    unfold ThR
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    have e : gl (ratS ℚ (σ r) * g) * dM u = gl (ratS ℚ (σ r)) * (gl g * dM u) := by rw [glm, mul_assoc]
    unfold Un.Uu
    rw [e, hleft]
    simp only [row_rat]
    rw [hσ r]
  simp only [e1]
  rw [key, Meas.I0, ← hmp.integral_comp hme]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have e2 : ∀ b, gl (nU b * (mD (Un.aa t u p.1) * cD u p.2)) * dM u =
      gl (nU b) * (gl (mD (Un.aa t u p.1)) * dM u * gl p.2) := by
    intro b
    rw [glm, glm, mul_assoc, mul_assoc, M.gl_cD, mul_assoc]
  simp only [iw, Un.Tt, Un.Uu, Un.Fb, e2, row_nU]
  rw [integral_mul_const, ← mul_assoc]
  simp only [map_mul (em E) (gl (nU _))]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.twisted_zeta_integral_at_compact_eq_at_rotation :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ (s : ℂ), ∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        Yt D χ φ s (gl k) = Yt D χ φ s (rot t) := by
  intro E _ _ _ D P ω χ hC hU hχ L N hL φ hA hG s k hk hS t hs hc
  obtain ⟨b, ζ, κ, hζ, hκ, hdec⟩ := UpperTheory.exists_unipotent_diag_rotation_level_decomposition N hG.pos k hk hS t hs hc
  have hab : ab ζ = 1 := UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles.2.2.1 ζ hζ
  have habm : ∀ y : (A ℚ)ˣ, ab (y * ζ ^ 2) = ab y := by
    intro y
    have h1 : IdeleGroup.ideleModule ℚ ζ = 1 := Subtype.ext hab
    show ((IdeleGroup.ideleModule ℚ (y * ζ ^ 2) : {r : ℝ // 0 < r}) : ℝ) = _
    rw [map_mul, map_pow, h1, one_pow, mul_one]
    rfl
  have hχω : ((ω.1 ζ⁻¹ : ℂˣ) : ℂ) ^ 2 = ((χ.1 ζ : ℂˣ) : ℂ) ^ 2 := by
    have h := hχ ζ
    have h2 : (ω.1 ζ⁻¹) ^ 2 = (χ.1 ζ) ^ 2 := by
      rw [map_inv, inv_pow, inv_eq_iff_mul_eq_one, ← mul_pow, mul_comm]
      exact h
    exact_mod_cast congrArg (fun u : ℂˣ => (u : ℂ)) h2
  let Gf : IdeleGroup ℚ → ℂ := fun y => Wo D φ (em E (aE y * rot t)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1)
  have key : ∀ y : IdeleGroup ℚ, Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) = Gf (y * ζ ^ 2) := by
    intro y
    rw [hdec, UpperTheory.whittaker_diagTorus_mul_iwasawa_eq E D ω φ hA N hG.lev y ζ b (rot t) κ hκ, hχω]
    show _ = Wo D φ (em E (aE (y * ζ ^ 2) * rot t)) * ((χ.1 (y * ζ ^ 2) : ℂˣ) : ℂ) * ((ab (y * ζ ^ 2) : ℝ) : ℂ) ^ (s - 1)
    have hχm : χ.1 (y * ζ ^ 2) = χ.1 y * χ.1 ζ ^ 2 := by rw [map_mul, map_pow]
    rw [habm, hχm]
    push_cast
    ring
  unfold Yt
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact integral_mul_right_eq_self Gf (ζ ^ 2)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem aE_mul' {K : Type} [Field K] [NumberField K] (x y : (A K)ˣ) : aE (x * y) = aE x * aE y := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aE, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.exists_whittaker_hecke_eigenvalues_and_coeff_eq_convolution :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∃ μ : ℕ → ℂ,
        (∀ n, 0 < n → n.Coprime N → ∀ r t : ℝ, r ≠ 0 →
          Wo D φ (em E (aE (iy r * pin n) * rot t)) = μ n * Wo D φ (em E (aE (iy r) * rot t))) ∧
        ((∃ r t : ℝ, r ≠ 0 ∧ Wo D φ (em E (aE (iy r) * rot t)) ≠ 0) → ∀ n, n ≠ 0 → a n = LSeries.convolution (bN N χ μ) (sqN N) n) := by
  intro E _ _ _ D P ω χ hCen hU hχω L N hχ φ hA hG a hIs
  obtain ⟨hpr, hex, hinj, hbad⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  obtain ⟨pmul, ppow⟩ := UpperTheory.ideleOfNat_mul_and_prime_pow
  have pin1 : pin 1 = 1 := by
    have := pmul 1 1 one_pos one_pos
    rw [one_mul] at this
    exact mul_eq_left.1 this.symm
  have pack : ∀ v : H.P ℚ, ¬ Bad N v → ∃ m : ℕ → ℂ, m 0 = 1 ∧ (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧ ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := fun v hv => by
    rcases UpperTheory.inert_or_split_of_good_delta_rat E D v (hG.pl v hv) with ⟨w, hw, hI⟩ | ⟨w, w', hne, hw, hw', hs, hs', hall⟩
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w hw hI
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_split_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w w' hne hw hw' hs hs' hall
  choose! M hM0 hM1 hM2 using pack
  obtain ⟨μ, hμ1, hμm, hμp⟩ := UpperTheory.exists_multiplicative_of_prime_power_values (fun v k => if Bad N v then 1 else M v k) (fun v => by
    by_cases h : Bad N v
    · simp [h]
    · simp [h, hM0 v h])
  have hpN : ∀ v : H.P ℚ, ¬ normV v ∣ N → ¬ Bad N v := fun v h hb => h ((hbad N v).1 hb)
  have hμv : ∀ (v : H.P ℚ) (k : ℕ), ¬ Bad N v → μ (normV v ^ k) = M v k := fun v k h => by
    have := hμp v k
    simpa [h] using this
  refine ⟨μ, ?_, ?_⟩
  · intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hc r t hr
      by_cases h1 : n = 1
      · subst h1
        rw [pin1, mul_one, hμ1, one_mul]
      have hp : n.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨k, m, hnd, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' n.minFac hp.ne_one
      obtain ⟨v, hv⟩ := hex _ hp
      have hk : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hnm
        exact hnd (hnm ▸ Nat.minFac_dvd n)
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by
        rintro rfl
        simp at hnm
        omega)
      have hmlt : m < n := by
        have h2 : 2 ≤ n.minFac ^ k := by
          calc 2 ≤ n.minFac := hp.two_le
            _ = n.minFac ^ 1 := (pow_one _).symm
            _ ≤ n.minFac ^ k := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hk)
        nlinarith
      have hmc : m.Coprime N := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hnm.symm) hc
      have hvb : ¬ Bad N v := hpN v fun h =>
        Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd n) (hv ▸ h) hc
      have hcop : (normV v ^ k).Coprime m :=
        Nat.Coprime.pow_left k (by rw [hv]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
      have hpin : pin n = pv v ^ k * pin m := by
        rw [hnm, ← hv, pmul _ _ (pow_pos (hpr v).pos k) hm0, ppow]
      have hg : em E (aE (iy r * pin n) * rot t) = em E (aE (pv v ^ k)) * em E (aE (iy r * pin m) * rot t) := by
        rw [hpin, mul_left_comm, aE_mul', map_mul, map_mul, map_mul, mul_assoc]
      have hnv : n = normV v ^ k * m := by rw [hv]; exact hnm
      rw [hg, hM1 v hvb k _ (fun w hw => UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd E v m r t hm0 (by rw [hv]; exact hnd) w hw), ih m hmlt hm0 hmc r t hr,
        ← mul_assoc, ← hμv v k hvb, ← hμm _ _ (pow_pos (hpr v).pos k) hm0 hcop, ← hnv]
  · rintro ⟨r, t, hr, hne⟩ n hn
    refine UpperTheory.eq_convolution_squareIndicator_of_euler_factors N a (bN N χ μ) hG.pos hIs.one hIs.mul hIs.bad ?_ ?_ ?_ ?_ n hn
    · simp [bN, pin1, hμ1]
    · intro x y hx hy hxy
      simp only [bN, Nat.coprime_mul_iff_left]
      by_cases h1 : x.Coprime N
      · by_cases h2 : y.Coprime N
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, pmul x y hx hy, hμm x y hx hy hxy, map_mul, Units.val_mul]
          push_cast
          ring
        · rw [if_neg fun h => h2 h.2, if_neg h2, mul_zero]
      · rw [if_neg fun h => h1 h.1, if_neg h1, zero_mul]
    · intro x hx
      simp only [bN]
      rw [if_neg hx]
    · intro p hp hpn
      obtain ⟨v, rfl⟩ := hex p hp
      have hvb := hpN v hpn
      rw [hM2 v hvb ⟨_, hne⟩]
      congr 1
      funext k
      have hc : (normV v ^ k).Coprime N := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
      simp only [bN, if_pos hc]
      rw [ppow, map_pow, Units.val_pow_eq_pow_val, hμv v k hvb]
      rfl
end
