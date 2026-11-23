module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle093
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCSplit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle010
public import Formalism.HermitianCurvature.StatementTL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
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

@[expose] public section

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section bd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibBd_term (Bs : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound Bs (fib j)) {o κ : ℕ} {Dop : B.DiffOp k r Wp Wq} (hIn : C6.InDDPlus Bs fib ∅ o κ Dop)
    (T' : B.DTerm k r Wp Wq) (hT' : LeibTerm Bs Dop T') {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖T'.coef g (B.Rw T'.word F g)‖ ≤
          K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
  obtain ⟨T, hT, Pc, j, hPc, hsub, hco'⟩ := hT'
  obtain ⟨Pp, a, bb, c, es, hP, hab, hlen, hlie, hco⟩ := hIn.2.2 T hT
  set S : Set (B.Mat k r) := {g | g ∈ B.GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} with hSdef
  set c₀ : ℝ := min ε (ε ^ 2) with hc₀
  have hc₀p : 0 < c₀ := lt_min hε (by positivity)
  have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (r + 2))) ∨ l = Fin.last (r + 1)) →
      c₀ ≤ Complex.normSq (Dmin k r Bs.z Bs.z' g l) := by
    intro g hg l hl
    rcases hl with hl | rfl
    · simp at hl
    · have := Formalism.FourierDecayAlt.P.gram_function_last_minor k r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g ε hg.2
      exact (min_le_left _ _).trans this
  have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ) := by
    intro g hg
    rw [Complex.normSq_ofReal]
    have h1 := hg.2
    have : ε ^ 2 ≤ Gf k r Bs.z Bs.z' g * Gf k r Bs.z Bs.z' g := by nlinarith
    exact (min_le_right _ _).trans this
  have hcU := P.AdmissibleLieWords.ubl_coefP Bs fib hfib ∅ Pp a bb c es hP hab hlie hε (fun g hg => hg) hc₀p hSD hSGf 0
  obtain ⟨⟨Cc, hCc0, hUB⟩, -⟩ := hcU
  set fo := (es.map fun e => e.2.length).sum with hfo
  obtain ⟨CP, hCP0, hCP⟩ := hPc.2 [] (fun x hx => by simp at hx)
  set D : ℕ := (2 * r + 2) * T.word.length with hD
  set cw : ℝ := (T'.word.map P.BetaSesquilinearity.nz).prod with hcw
  have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
    obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (P.BetaSesquilinearity.nz_pos X).le
  refine ⟨CP * ε⁻¹ ^ j * Cc * cw, by positivity, fun F A b hF g hg hgε => ?_⟩
  have hgS : g ∈ S := ⟨hg, hgε⟩
  have hgp := P.BetaSesquilinearity.gN_pos hg
  have hg1 := P.BetaSesquilinearity.gN_ge_one hg
  have hGpos : 0 < Gf k r Bs.z Bs.z' g := lt_of_lt_of_le hε hgε
  have hgd : g ∈ C6.domL Bs ∅ := ⟨hg, hGpos, fun l hl => by simp at hl⟩
  have hAdm0 : PI.UnitaryCorollaryDerivatives.CRH.admitted (k := k) (r := r) 0 [] := ⟨[], [], by simp, by simp, by simp, by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR]⟩
  have hc1 : ‖T.coef g‖ ≤ Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0) := by
    have h := hUB [] hAdm0 g hgS
    have e : P.BetaSesquilinearity.Dw [] (fun g => (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g) g =
        (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g := rfl
    rw [e] at h
    rw [hco g hgd]
    simpa using h
  have hb0 : 0 ≤ b := by
    have h := hF.2 [] [] (by simp) (by simp) (by simp) g hg
    exact le_trans (by positivity) h
  have hc2 : ‖B.Rw T'.word F g‖ ≤ cw * (b * B.gN g ^ (-A)) := by
    rw [P.BetaSesquilinearity.Rw_scale]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hunit : ∀ X ∈ T'.word.map P.BetaSesquilinearity.nrm, B.unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact P.BetaSesquilinearity.nrm_unit (T'.word_lie Y hY)
    have hl' : T'.word.length ≤ T.word.length := hsub.length_le
    have h := hF.2 [] (T'.word.map P.BetaSesquilinearity.nrm) (by simp) hunit (by simp; omega) g hg
    have e : B.dLR [] (T'.word.map P.BetaSesquilinearity.nrm) F g = B.Rw (T'.word.map P.BetaSesquilinearity.nrm) F g := rfl
    rw [e] at h
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos hgp _
    rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ hpw, mul_comm]
    exact h
  have hc3 : ‖Pc g‖ ≤ CP * B.gN g ^ D := by
    have := hCP g hg
    simpa [P.B4.W_nil] using this
  have hc4 : ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ ≤ ε⁻¹ ^ j := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hε hgε) j
  have hfo' : fo ≤ o := by omega
  have hwo : T.word.length ≤ o := by omega
  rw [hco' g hgd, ContinuousLinearMap.smul_apply, norm_smul, norm_mul]
  calc ‖Pc g‖ * ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ * ‖T.coef g (B.Rw T'.word F g)‖
      ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j * (‖T.coef g‖ * ‖B.Rw T'.word F g‖) := by
        gcongr
        exact (T.coef g).le_opNorm _
    _ ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j *
          ((Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)) * (cw * (b * B.gN g ^ (-A)))) := by
        gcongr
    _ = CP * ε⁻¹ ^ j * Cc * cw * b *
          (B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ)) * B.gN g ^ (-A)) := by
        rw [Real.rpow_natCast]; ring_nf
    _ = CP * ε⁻¹ ^ j * Cc * cw * b * B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ) - A) := by
        rw [← Real.rpow_add hgp, sub_eq_add_neg]
    _ ≤ CP * ε⁻¹ ^ j * Cc * cw * b *
          B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hg1
        have h3 : (3 * (r + 1) * fo : ℕ) ≤ 3 * (r + 1) * o := Nat.mul_le_mul_left _ hfo'
        have h4 : ((3 * (r + 1) * fo : ℕ) : ℝ) ≤ ((3 * (r + 1) * o : ℕ) : ℝ) := by exact_mod_cast h3
        have h5 : (D : ℝ) ≤ ((2 * r + 2) * o : ℕ) := by
          rw [hD]; exact_mod_cast Nat.mul_le_mul_left _ hwo
        push_cast at h4 h5 ⊢
        linarith

theorem leibniz_bound_holds : NFLeibBd := by
  unfold NFLeibBd
  intro k r Wp Wq _ _ _ _ _ Bs nf fib o κ Dop hfib hIn L hL ε hε
  induction L with
  | nil =>
    refine ⟨0, le_refl _, ?_⟩
    intro F A b hF g hg hεg
    simp [B.opApply]
  | cons T L ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := nfLeibBd_term Bs fib hfib hIn T (hL T (by simp)) hε
    obtain ⟨K₂, hK₂, h₂⟩ := ih (fun T' hT' => hL T' (by simp [hT']))
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    intro F A b hF g hg hεg
    have e1 := h₁ F A b hF g hg hεg
    have e2 := h₂ F A b hF g hg hεg
    have hs : B.opApply (T :: L) F g = T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      simp [B.opApply]
    rw [hs]
    calc _ ≤ ‖T.coef g (B.Rw T.word F g)‖ + ‖B.opApply L F g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring

end bd

end Formalism.FourierDecayAlt.P.CutBP
end
end

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

theorem norm_psiG (g : ℝ) (l c : ℂ) : ‖psiG g l c‖ = 1 := by
  simp only [psiG]
  rw [Complex.norm_exp]
  simp

theorem continuous_psiG (g : ℝ) (l : ℂ) : Continuous (psiG g l) := by
  unfold psiG
  fun_prop

theorem psi_prod (g : ℝ) (hg : g ≠ 0) (σ z : crystallineComparison.V f) :
    crystallineComparison.psi (σ * z) = ∏ v, psiG g ((g • σ) v) (z v) := by
  have key : ∀ v, (2 * (((g • σ) v) * z v).re / g : ℝ) = 2 * (σ v * z v).re := by
    intro v
    rw [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
    field_simp
  simp only [psiG, key]
  rw [← Complex.exp_sum, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair, Complex.ofReal_sum,
    Finset.mul_sum]

theorem integrable_mul_psiG {φ : ℂ → ℂ} (hφ : Integrable φ) (g : ℝ) (l : ℂ) :
    Integrable fun c => φ c * psiG g l c := by
  refine hφ.norm.mono' (hφ.aestronglyMeasurable.mul (continuous_psiG g l).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun c => by rw [norm_mul, norm_psiG, mul_one]

theorem fourier_Nz (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : g ≠ 0) (dl : Fin f → ℝ)
    (hdl : ∀ v, dl v ≠ 0) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c) (σ : crystallineComparison.V f) :
    crystallineComparison.fourier (Nz Y κ D) σ = (∏ v, ((dl v : ℝ) : ℂ)) * Hh Y κ hat (g • σ) := by
  have hae : (fun z => ((Nz Y κ D z : ℝ) : ℂ) * crystallineComparison.psi (σ * z)) =ᵐ[volume]
      fun z => Fz Y κ D z * crystallineComparison.psi (σ * z) := by
    filter_upwards [ae_good] with z hz
    have h0 := Complex.nonneg_iff.mp (Fz_nonneg Y κ hκ D hD z hz)
    rw [Nz, if_pos hz]
    congr 1
    exact Complex.ext (by simp) (by simp [← h0.2])
  have hpt : ∀ z : crystallineComparison.V f, Fz Y κ D z * crystallineComparison.psi (σ * z) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v)) := by
    intro z
    rw [Fz, psi_prod g hg σ z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  have hone : ∀ v h h', ∫ c, D v h h' c * psiG g ((g • σ) v) c =
      ((dl v : ℝ) : ℂ) * hat v ((g • σ) v) h h' := by
    intro v h h'
    rw [hhat, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hdl v), one_mul]
  have hint : ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z : crystallineComparison.V f =>
      κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v))) := by
    intro h hh h' hh'
    exact (Integrable.fintype_prod (fun v => integrable_mul_psiG (hDi v h hh h' hh') g _)).const_mul _
  unfold crystallineComparison.fourier
  rw [integral_congr_ae hae]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun h hh => integrable_finsetSum _ (fun h' hh' => hint h hh h' hh')),
    Hh, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [integral_finsetSum _ (fun h' hh' => hint h hh h' hh'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h' hh' => ?_
  have hp := integral_fintype_prod_volume_eq_prod (fun v (c : ℂ) => D v h h' c * psiG g ((g • σ) v) c)
  rw [integral_const_mul, hp]
  simp_rw [hone]
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_good (τ : crystallineComparison.V f) : ∃ x : crystallineComparison.V f, Good x ∧ Good (x + τ) := by
  refine ⟨fun v => ((‖τ v‖ + 1 : ℝ) : ℂ), fun v => ?_, fun v => ?_⟩
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) ≠ 0
    have hpos : (0 : ℝ) < ‖τ v‖ + 1 := by positivity
    exact_mod_cast hpos.ne'
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) + τ v ≠ 0
    intro h
    have h2 : τ v = -(((‖τ v‖ + 1 : ℝ) : ℂ)) := by linear_combination h
    have h3 := congrArg (fun w : ℂ => ‖w‖) h2
    simp only [norm_neg] at h3
    rw [Complex.norm_of_nonneg (by positivity)] at h3
    linarith

theorem herglotz_germ (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (hat : Fin f → ℂ → H → H → ℂ)
    (hG : GermData Y U P Q hat)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (Lm : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology Lm] [IsZLattice ℝ Lm]
    (hLm : ∀ σ ∈ crystallineComparison.dualSet La, g • σ ∈ Lm) (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V f, Good x → Good (x + g • σ) → ‖phi Y κ U x (x + g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  obtain ⟨LIM, hL⟩ := Formalism.FourierDecayAlt.P.invariantMeanExists f Lm
  have hbd : ∀ σ ∈ crystallineComparison.dualSet La,
      ‖Hh Y κ hat (g • σ) + A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)‖ ≤ F σ := by
    intro σ hσ
    rw [← mean_split Lm.toAddSubgroup LIM hG κ hκ hL (g • σ)]
    refine Formalism.FourierDecayAlt.P.mean_bound_estimate _ LIM _ (F σ) hL.1 ?_
    intro x
    unfold phiG
    split_ifs with hx
    · exact hF σ hσ x hx.1 hx.2
    · obtain ⟨x0, h1, h2⟩ := exists_good (g • σ)
      simpa using (norm_nonneg _).trans (hF σ hσ x0 h1 h2)
  let A : crystallineComparison.V f → ℂ := fun σ => ((∏ v, dl v : ℝ) : ℂ) * A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) A := by
    intro T w hT
    have hinj : Set.InjOn (fun σ : crystallineComparison.V f => g • σ) T :=
      fun a _ b _ hab => smul_right_injective (crystallineComparison.V f) hgne hab
    have hT' : ∀ τ ∈ T.image (fun σ : crystallineComparison.V f => g • σ), τ ∈ Lm.toAddSubgroup := by
      intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      exact hLm σ (hT σ hσ)
    have h0 := limit_average_positive_definite Lm.toAddSubgroup LIM hG κ hκ hL.1 (T.image (fun σ : crystallineComparison.V f => g • σ)) hT'
      (fun τ => w (g⁻¹ • τ))
    simp_rw [Finset.sum_image hinj] at h0
    simp only [inv_smul_smul₀ hgne, ← smul_sub] at h0
    have hsplit : (∑ σ ∈ T, ∑ σ' ∈ T, A (σ - σ') * w σ * starRingEnd ℂ (w σ')) =
        ((∏ v, dl v : ℝ) : ℂ) * ∑ σ ∈ T, ∑ σ' ∈ T,
          A0 Lm.toAddSubgroup LIM Y κ U P Q (g • (σ - σ')) * w σ * starRingEnd ℂ (w σ') := by
      simp only [A, Finset.mul_sum, mul_assoc]
    rw [hsplit, Complex.re_ofReal_mul]
    exact mul_nonneg hc0 h0
  have hb : ∀ σ : crystallineComparison.dualSet La, ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [hfour]
    simp only [A]
    rw [← mul_add, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hbd σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) A (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

theorem herglotz_plain (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La] (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ‖Hh Y κ hat (g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) (0 : crystallineComparison.V f → ℂ) := by
    intro T w _
    simp
  have hb : ∀ σ : crystallineComparison.dualSet La,
      ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [Pi.zero_apply, add_zero, hfour, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hF σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) 0 (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

end

end Formalism.FourierDecayAlt.P.PBC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

def PolyRadial : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Complex.normSq ζ : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def ModConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c₁ c₂ : ℝ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        ‖B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf))‖ ^ 2 = c₁ * ‖B.hsVec Xf‖ ^ 2 ∧
        ‖B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf))‖ ^ 2 =
          c₂ * ‖B.hsVec Xf‖ ^ 2

def LineNonzero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ (π : M.Ty P), ∀ ζ ∈ Gauge.GC.Ann P, ∃ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf ∧ Xf ≠ 0

def PolyFinish : Prop :=
  ∀ (q : Polynomial ℂ) (n : ℕ) (a C : ℝ),
    (∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) →
    ∃ c : ℂ, q = Polynomial.C c * (Polynomial.X - Polynomial.C (a : ℂ)) ^ n

def ThConstOfCut : Prop := PolyRadial → ModConst → LineNonzero → PolyFinish → ThConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

noncomputable section

theorem lift_of_x_of_parts : TL.LiftXOfParts := by
  intro hZ _hC hX Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨_, _, hAct, hQQ, _, _, _, hLS⟩ := hD
  obtain ⟨B0, _, hB⟩ := hX Wp Wq P Bs X
  obtain ⟨hFB, hEq, hRad⟩ := hB Y
  set E := xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) with hE
  set s : ℂ := M.sgn P l0 with hs
  have hx : st.x Y = L.GGi * st.QQ Y 1 1 := by
    rw [hLS.tau, ← mul_assoc, L.GGi_GG, one_mul]
  have hx1 : (st.x Y).1 = X.fn 5 * (s • X.t Y 1 1) := by
    rw [hx, hQQ Y, hAct.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  refine hZ Wp Wq P Bs 0 0 0 0 (fun _ => s) E (st.x Y) ?_ hFB ?_ ?_
  · refine ⟨MvPolynomial.C s, by simp, fun g => by simp⟩
  · intro p hp g hg J
    simp only [pow_zero, mul_one, smul_apply]
    rw [hEq p hp g hg J, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx'
    simp only [pow_zero, mul_one, smul_apply]
    rw [hx1, Module.End.mul_apply, X.fn_apply 5 _ x hx', LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      Pi.smul_apply, hRad Φ x hx', smul_smul, smul_smul]
    have hG : (0 : ℝ) < Q.GGl P.k P.r Bs.z Bs.z' x.2 := hx'.2.2
    simp only [Q.fnVal]
    congr 1
    have hG' : ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp

end

end Formalism.FourierDecayAlt.P
end
