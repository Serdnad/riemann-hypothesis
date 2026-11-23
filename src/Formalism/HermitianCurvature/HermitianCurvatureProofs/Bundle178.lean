module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open Complex

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_exp_mul_I_sub_one (y : ℝ) : ‖Complex.exp ((y : ℂ) * I) - 1‖ ≤ |y| := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hs := Real.sin_sq_add_cos_sq y
  have e : (↑(Real.cos y) + ↑(Real.sin y) * I - 1 : ℂ) = ↑(Real.cos y - 1) + ↑(Real.sin y) * I := by
    push_cast; ring
  rw [e]
  have h2 : ‖(↑(Real.cos y - 1) + ↑(Real.sin y) * I : ℂ)‖ ^ 2 ≤ |y| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I, sq_abs]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h2

theorem norm_exp_sub_one_of_re (z : ℂ) (hz : z.re = 0) : ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  have hz' : z = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hz]
  rw [hz']
  refine (norm_exp_mul_I_sub_one z.im).trans (le_of_eq ?_)
  rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem iter_add_const {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (i : ℕ) (f : E → F) (c : F) (x : E) :
    iteratedFDeriv ℝ (i + 1) (fun y => f y + c) x = iteratedFDeriv ℝ (i + 1) f x := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  congr 2
  funext y
  exact fderiv_add_const c

variable {k r : ℕ}

theorem mult_phase {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (D : Mat k r →L[ℝ] ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (F : Mat k r → E) (c : ℝ),
      CCle (A + ((m + 1 : ℕ) : ℝ)) m F c →
      CCle A m (fun g => (Complex.exp (PBFV.phaseL σ D g) - 1) • F g) (K * ‖σ‖ * c) := by
  obtain ⟨C1, hC1, hdlr⟩ := Formalism.FourierDecayAlt.P.JCx4.dlr_bound (k := k) (r := r) (E := E →L[ℂ] E) m
  obtain ⟨K0, hK0⟩ : ∃ K : ℝ, ∀ M : Mat k r, ‖D M‖ ≤ K * ‖M‖ := ⟨_, D.le_opNorm⟩
  set KD : ℝ := max K0 0 with hKDdef
  have hKD0 : 0 ≤ KD := le_max_right _ _
  have hKD : ∀ M : Mat k r, ‖D M‖ ≤ KD * ‖M‖ := fun M =>
    (hK0 M).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set Lid : ℂ →L[ℝ] (E →L[ℂ] E) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℂ E) with hLid
  set L : ℝ := 1 + 4 * KD with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  set K : ℝ := 2 ^ m * (C1 * (2 ^ m * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (2 * KD * (1 + L ^ m)))))) with hKdef
  refine ⟨K, by positivity, ?_⟩
  intro σ hσ A F c hF
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hF
  set θ : Mat k r →L[ℝ] ℂ := PBFV.phaseL σ D with hθdef
  have hθ0 : ∀ g, (θ g).re = 0 := PBFV.phaseL_re σ D
  set t : ℝ := 2 * ‖σ‖ * KD with htdef
  have ht0 : 0 ≤ t := by positivity
  have htL : t ≤ L := by
    rw [htdef, hLdef]
    have : ‖σ‖ * KD ≤ 2 * KD := mul_le_mul_of_nonneg_right hσ hKD0
    linarith
  have hθM : ∀ M : Mat k r, ‖θ M‖ ≤ t * ‖M‖ := by
    intro M
    rw [hθdef, PBFV.phaseL_apply]
    calc ‖σ * D M - (starRingEnd ℂ) (σ * D M)‖ ≤ ‖σ * D M‖ + ‖(starRingEnd ℂ) (σ * D M)‖ := norm_sub_le _ _
      _ = 2 * (‖σ‖ * ‖D M‖) := by rw [Complex.norm_conj, norm_mul]; ring
      _ ≤ 2 * (‖σ‖ * (KD * ‖M‖)) := by gcongr; exact hKD M
      _ = t * ‖M‖ := by rw [htdef]; ring
  have hθK := θ.opNorm_le_bound ht0 hθM
  have hexp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  set f0 : Mat k r → ℂ := fun g => Complex.exp (θ g) with hf0def
  have hf0 : ContDiff ℝ ⊤ f0 := hexp.comp θ.contDiff
  have hit0 : ∀ i g, ‖iteratedFDeriv ℝ i f0 g‖ ≤ t ^ i := by
    intro i g
    have h2 : iteratedFDeriv ℝ i f0 g =
        (iteratedFDeriv ℝ i Complex.exp (θ g)).compContinuousLinearMap (fun _ => θ) :=
      θ.iteratedFDeriv_comp_right (f := Complex.exp) hexp g (by exact_mod_cast le_top)
    have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ i Complex.exp (θ g)) (fun _ : Fin i => θ)
    have h5 := h3.trans (mul_le_mul (le_of_eq (by rw [PBFV.norm_iter_cexp, hθ0, Real.exp_zero]))
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hθK))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
    rw [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
    rw [h2]; exact h5
  set f1 : Mat k r → ℂ := fun g => f0 g + (-1 : ℂ) with hf1def
  have hf1 : ContDiff ℝ ⊤ f1 := hf0.add contDiff_const
  set Λ : Mat k r → (E →L[ℂ] E) := fun g => Lid (f1 g) with hΛdef
  have hΛ : ∀ g, Λ g = (Complex.exp (θ g) - 1) • ContinuousLinearMap.id ℂ E := fun g => by
    simp [Λ, Lid, f1, f0, sub_eq_add_neg]
  have hΛc : ContDiff ℝ ⊤ Λ := Lid.contDiff.comp hf1
  have hitΛ : ∀ i, i ≤ m → ∀ g, ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * (t * (‖g‖ + L ^ m)) := by
    intro i hi g
    have h1 := Lid.norm_iteratedFDeriv_comp_left (f := f1) (x := g) (N := ⊤) (n := i)
      hf1.contDiffAt (by exact_mod_cast le_top)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rcases i with _ | j
    · rw [norm_iteratedFDeriv_zero]
      have e1 : f1 g = Complex.exp (θ g) - 1 := by simp [f1, f0, sub_eq_add_neg]
      rw [e1]
      calc ‖Complex.exp (θ g) - 1‖ ≤ ‖θ g‖ := norm_exp_sub_one_of_re _ (hθ0 g)
        _ ≤ t * ‖g‖ := hθM g
        _ ≤ t * (‖g‖ + L ^ m) := by
          have : 0 ≤ L ^ m := by positivity
          nlinarith
    · rw [show f1 = fun y => f0 y + (-1 : ℂ) from rfl, iter_add_const]
      calc ‖iteratedFDeriv ℝ (j + 1) f0 g‖ ≤ t ^ (j + 1) := hit0 _ g
        _ = t * t ^ j := by ring
        _ ≤ t * L ^ m := by
          refine mul_le_mul_of_nonneg_left ?_ ht0
          calc t ^ j ≤ L ^ j := pow_le_pow_left₀ ht0 htL j
            _ ≤ L ^ m := pow_le_pow_right₀ hL1 (by omega)
        _ ≤ t * (‖g‖ + L ^ m) := by
          have : 0 ≤ ‖g‖ := norm_nonneg _
          nlinarith
  set Cm : ℝ := C1 * (2 ^ m * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (1 + L ^ m))))) with hCm
  have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
        ‖dLR u v Λ g‖ ≤ Cm * gN g ^ (((m + 1 : ℕ) : ℕ) : ℝ) := by
    intro u v hu hv hl g hg _
    rw [Real.rpow_natCast]
    have h1 := hdlr Λ (hΛc.of_le (by exact_mod_cast le_top)) u v hu hv hl g
    have hg1 : 1 ≤ gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    have hng : ‖g‖ ≤ gN g := Formalism.FourierDecayAlt.P.JCx2.mn_norm_le_gN g
    have hsum : ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ ≤
        ((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (‖g‖ + L ^ m))) := by
      calc ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖
          ≤ ∑ _i ∈ Finset.range (m + 1), ‖Lid‖ * (t * (‖g‖ + L ^ m)) :=
            Finset.sum_le_sum fun i hi => hitΛ i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) g
        _ = ((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (‖g‖ + L ^ m))) := by simp
    have hpow : (1 + ‖g‖) ^ m ≤ 2 ^ m * gN g ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hgL : ‖g‖ + L ^ m ≤ (1 + L ^ m) * gN g := by
      have : 0 ≤ L ^ m := by positivity
      nlinarith
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hLid0 : 0 ≤ ‖Lid‖ := norm_nonneg _
    calc ‖dLR u v Λ g‖ ≤ C1 * (1 + ‖g‖) ^ m * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ := h1
      _ ≤ C1 * (2 ^ m * gN g ^ m) * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * ((1 + L ^ m) * gN g)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC1) (hsum.trans ?_) hS0
          · exact mul_nonneg hC1 (by positivity)
          · gcongr
      _ = Cm * gN g ^ (m + 1) := by rw [hCm]; ring
  have ha : CkOn (m : ℕ∞) Set.univ Λ := fun g₀ _ =>
    ⟨Set.univ, Λ, isOpen_univ, trivial, (hΛc.of_le (by exact_mod_cast le_top)).contDiffOn, fun _ _ _ => rfl⟩
  have hb' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
    (A := A) (d := (((m + 1 : ℕ) : ℕ) : ℝ)) ha hab hF (fun g _ h => h.elim)
  have e : (fun g => (Complex.exp (PBFV.phaseL σ D g) - 1) • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap Λ F := by
    funext g
    simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ, θ]
  rw [e]
  refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (le_of_eq ?_)
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  rw [abs_of_nonneg hCm0, abs_of_nonneg hc0, hCm, hKdef, htdef]
  ring

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem asm_contOn_of_ckOn {r : ℕ} {m : ℕ∞} {F : B.Mat k r → E} (hF : B.CkOn m (B.GV k r) F) :
    ContinuousOn F (B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := (hF'.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := B.GV k r)).congr_of_eventuallyEq ?_ (hag g₀ hgU hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgG
  exact hag g hgU' hgG

theorem asm_star_cpt (j ρ : ℕ) (F : B.Mat k (j + ρ) → E) (hFc : B.CkOn ⊤ (B.GV k (j + ρ)) F)
    (R : ℝ) (hR : ∀ g ∈ B.GV k (j + ρ), F g ≠ 0 → B.gN g ≤ R) (χD : ℂ → ℂ) (hχ : U.IsCutC χD) (A₁ : ℝ)
    (hA₁ : 0 ≤ A₁) :
    ∃ B₁, U.Star k j ρ (fun g => χD (U.DjU k j ρ g) • F g) A₁ 0 B₁ ((fun w : ℂ => ‖w‖) '' tsupport χD) := by
  have hχc : Continuous χD := hχ.1.continuous
  have hDc := Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k j ρ
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hχ.2.1
  have hKc : IsCompact (B.GV k (j + ρ) ∩ {g : B.Mat k (j + ρ) | B.gN g ≤ R}) :=
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (j + ρ) R).inter_left (Formalism.FourierDecayAlt.P.unitary_group_closed k (j + ρ)).closed
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn ((asm_contOn_of_ckOn hFc).mono Set.inter_subset_left)
  refine ⟨(max R 0) ^ A₁ * (max Cχ 0 * max CF 0), ⟨?_, ?_, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hFc g₀ hg₀
    refine ⟨W0, fun g => χD (U.DjU k j ρ g) • F' g, hU, hgU, ?_, fun g hg hgG => by simp only [hag g hg hgG]⟩
    exact contDiffOn_zero.2 ((hχc.comp hDc).continuousOn.smul (hF'.continuousOn))
  · intro g _ hne
    refine ⟨U.DjU k j ρ g, subset_tsupport _ (fun h0 => hne ?_), rfl⟩
    simp only [h0, zero_smul]
  · intro u v hu hv hl g hg
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0 hv0
    show B.gN g ^ A₁ * ‖χD (U.DjU k j ρ g) • F g‖ ≤ _
    by_cases h0 : F g = 0
    · rw [h0, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · have hgR := hR g hg h0
      have hg0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
      refine mul_le_mul (Real.rpow_le_rpow hg0 (hgR.trans (le_max_left _ _)) hA₁) ?_ (norm_nonneg _)
        (Real.rpow_nonneg (le_max_right _ _) _)
      rw [norm_smul]
      exact mul_le_mul ((hCχ _).trans (le_max_left _ _)) ((hCF g ⟨hg, hgR⟩).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)

theorem asm_gInt_int (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ) (hd : ∀ i, d i ≠ 0) (ht : t ≠ 0)
    (z z' : Fin (2 * (ph + (0 + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (0 + 1) + ρ) → E)
    (hFc : B.CkOn ⊤ (B.GV k (ph + (0 + 1) + ρ)) F) (R : ℝ)
    (hR : ∀ g ∈ B.GV k (ph + (0 + 1) + ρ), F g ≠ 0 → B.gN g ≤ R) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) := by
  have hw : (G.wMat (0 + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (0 + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (0 + 1) * (G.wMat (0 + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc₀
  have hR0 : (0 : ℝ) ≤ ((ph + (0 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA₁ : (0 : ℝ) ≤ 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
      (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) := by positivity
  obtain ⟨B₁, hStar⟩ := asm_star_cpt (ph + (0 + 1)) ρ F hFc R hR χD hχD _ hA₁
  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    have := norm_pos_iff.mpr hc₀
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
        (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) /
        (8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1)) := by
    rw [mul_div_cancel_left₀ _ (by positivity)]
    linarith
  have h1 := Formalism.FourierDecayAlt.P.JCTx6.Int.intG k ph 0 ρ σ d t hd ht _ hK hK0 0 _ hthr z z' E _ B₁ hStar γ hγ
  have e : Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ =
      Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' (fun g => χD (U.DjU k (ph + (0 + 1)) ρ g) • F g) γ := by
    funext y
    have hdet : G.detM (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) = t ^ (0 + 1) * (G.wMat (0 + 1)).det :=
      Formalism.FourierDecayAlt.P.JCTx6.Pos.detM_Zv 0 t y.2.2
    have hD : U.DjU k (ph + (0 + 1)) ρ (U.gaXi (p := ph) (s := 0 + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) γ) = c₀ := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hdet]
    simp only [Formalism.FourierDecayAlt.P.JCTx6.gInt]
    rw [hD, hχD1 c₀ (by rw [dist_self]; positivity), one_smul]
  rw [e]; exact h1

theorem integrable_unipotent_rank_one (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (c : ℂ)
    (z z' : Fin (2 * (ph + 1 + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + 1 + ρ) → E) (γ : B.Mat k ρ)
    (h : Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d c z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ)) :
    Integrable (fun ξ : U.Xi k ph 1 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ))
      (U.muXi k ph 1 ρ σ) := by
  have hE : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  let v₀ : G.UT (0 + 1) → ℂ := fun q => isEmptyElim q
  have hvol : (volume : Measure (G.UT (0 + 1) → ℂ)) = Measure.dirac v₀ := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  have a1 : SigmaFinite (volume : Measure (Fin (0 + 1) → Fin ph → ℂ)) := inferInstance
  have a2 : SigmaFinite (volume : Measure (Fin ph → Fin (0 + 1) → ℂ)) := inferInstance
  have a3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
  have b1 : SigmaFinite (volume : Measure ((Fin (0 + 1) → Fin ph → ℂ) × (Fin ph → Fin (0 + 1) → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b2 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : SigmaFinite (volume : Measure (U.XiH ph (0 + 1) σ)) := by
    haveI := b1; haveI := b2
    rw [Measure.volume_eq_prod]; infer_instance
  have b4 : SigmaFinite (U.muXiH ph (0 + 1) σ) := by unfold U.muXiH; exact b3
  have hg : MeasurePreserving (fun b : U.XiH ph (0 + 1) σ => (b, v₀)) volume
      ((volume : Measure (U.XiH ph (0 + 1) σ)).prod (volume : Measure (G.UT (0 + 1) → ℂ))) := by
    rw [hvol]
    exact ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SL.sigma_RC k (ph + (0 + 1)) ρ
  have hφ : MeasurePreserving (Prod.map (id : U.RC k (ph + (0 + 1)) ρ × U.RC k (ph + (0 + 1)) ρ → _)
      (fun b : U.XiH ph (0 + 1) σ => (b, v₀))) (U.muXi k ph 1 ρ σ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) :=
    (MeasurePreserving.id _).prod hg
  have h2 := (hφ.integrable_comp h.aestronglyMeasurable).2 h
  refine h2.congr (ae_of_all _ fun ξ => ?_)
  have hs : G.superSum (G.upper v₀) = 0 := by simp [G.superSum]
  have hZ : (Matrix.of.symm (c • G.wMat (0 + 1) * G.upper v₀) : G.Mat (0 + 1)) = fun _ _ => c := by
    funext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  simp only [Function.comp_apply, Prod.map, id, Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]
  simp [G.psi]

end Formalism.FourierDecayAlt.P.PBH
end
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

def FormOne : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (X : Q.ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt (JC.parLev P0 j).k (JC.parLev P0 j).r))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π')) (JC.parLev P0 j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π'))) (l0 : ℕ),
    P5.IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 →
    KB.ZetaNorm (T.bs j) μ →
    ∀ (w : List C.Letter) (F F' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ Φ' : Wd.Ix (Fin w.length) →
        Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (ε : ℝ),
      0 < ε → (∀ a, JC.NiceCoef (T.bs j) ε (F a)) → (∀ a, JC.NiceCoef (T.bs j) ε (F' a)) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F a)) y.1 y.2) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ' a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F' a)) y.1 y.2) →
      D.formLev T (M.sgn P0 l0) j w F F' = P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ' 0

def ZetaNormExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq), ∃ μ : Measure (Mt k r), KB.ZetaNorm Bs μ

theorem integrable_of_decay4 {φ : ℂ → ℂ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) : Integrable φ := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(4 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine Integrable.mono' (hd.const_mul C) hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have e : (1 + ‖t‖) ^ (-4 : ℤ) = (1 + ‖t‖) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [← e]; exact hC t

theorem nice_common {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {S : Type} [Fintype S] (Bs : B.RealPlaceData k ρ Wp Wq)
    {x : S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : ∀ a, KB.CptCoef Bs (x a)) :
    ∃ ε, 0 < ε ∧ ∀ a, JC.NiceCoef Bs ε (x a) := by
  classical
  choose R hR using fun a => (h a).2.1
  choose εf hεf0 hεf using fun a => (h a).2.2
  let Sε : Finset ℝ := insert 1 (Finset.univ.image εf)
  have hne : Sε.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨Sε.min' hne, ?_, fun a => ⟨(h a).1, fun A m => ?_, fun g hg hg0 => ?_⟩⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεf0 a
  · refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G (h a).1 (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ (R a)) (fun g hg hgC => ?_) A m
    by_contra h0
    exact hgC (hR a g hg h0)
  · exact le_trans (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
      (hεf a g hg hg0)

end Formalism.FourierDecayAlt.P.PBO
end
end
