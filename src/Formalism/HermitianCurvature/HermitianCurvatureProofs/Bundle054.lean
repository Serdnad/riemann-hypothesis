module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle001

@[expose] public section

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7


theorem c2_section_decomp_of_pieces : C2.SectionDecompOfParts := by
  intro _ hC1iii hURI hUp _ hUM _ hTM k r z z' γ hstd hpos hmono s hs
  have hz := hstd.2.1
  have hU := hUM k r z hz
  have hSg := symmetric_group_holds k r z hz.1
  have hNg := unipotent_subgroup_holds k r

  have hu1 : C2.uMap k r z 1 = 1 := hU.2 1 (one_mem_UW z)
  have huinv : ∀ x ∈ Sset k r z, C2.uMap k r z x⁻¹ = (C2.uMap k r z x)⁻¹ := by
    intro x hx
    have hxi := hSg.2.2 x hx
    have hxu : IsUnit x.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hx)
    have : C2.uMap k r z x * C2.uMap k r z x⁻¹ = 1 := by
      rw [← (hU.1 x hx).2.2 _ hxi, Matrix.mul_nonsing_inv _ hxu, hu1]
    exact (Matrix.inv_eq_right_inv this).symm

  have huSg : ∀ σ ∈ C2.Sg k r z z' γ, σ ∈ Sset k r z ∧ ∃ v, v ∈ C2.UTset (r + 1) ∧ vᴴ ∈ C2.LPg (Zhat k r z z' γ) ∧
      C2.uMap k r z σ = v := by
    rintro σ ⟨n0, hn0, v, hv, hvL, h, hh, rfl⟩
    obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
    have hn0S : n0 ∈ Sset k r z := N_sub_S hn0.1
    have hτS : C2.tauM k r z v ∈ Sset k r z := N_sub_S hτN
    have hhS : h ∈ Sset k r z := UW_sub_S hh
    have hs1 := hSg.2.1 _ hn0S _ hτS
    refine ⟨hSg.2.1 _ hs1 _ hhS, v, hv, hvL, ?_⟩
    rw [(hU.1 _ hs1).2.2 h hhS, (hU.1 _ hn0S).2.2 _ hτS, hn0.2, hτu, hU.2 h hh, Matrix.one_mul, Matrix.mul_one]

  have hRimg : ∀ ρ ∈ C2.Rst k r z z' γ, C2.uMap k r z ρ ∈ C2.UTset (r + 1) ∧ (C2.uMap k r z ρ)ᴴ ∈ C2.Lstg (Zhat k r z z' γ) := by
    intro ρ hρ
    have hmap := (hC1iii k r z z' γ hstd hpos).1.mapsTo hρ
    obtain ⟨h1, h2, h3⟩ := hmap
    have : C2.uMap k r z ρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} :=
      ⟨h1, _, h2, h3⟩
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono] at this
    exact this
  have hRS : ∀ ρ ∈ C2.Rst k r z z' γ, ρ ∈ Sset k r z := fun ρ hρ => hρ.1.1
  obtain ⟨hus, husUT, _⟩ := hU.1 s hs
  obtain ⟨⟨uρ, v⟩, ⟨huρ, hv, huρL, hvL, hue⟩, huniq⟩ := hUp (r + 1) (Zhat k r z z' γ) hmono _ husUT
  simp only at huρ hv huρL hvL hue

  have huρR : uρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} := by
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono]; exact ⟨huρ, huρL⟩
  obtain ⟨u', hu', hu'e⟩ := huρR.2
  have hmemT : (uρ, u') ∈ {p : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ |
      p.1 ∈ C2.UTset (r + 1) ∧ p.2 ∈ C2.UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} :=
    ⟨huρ, hu', hu'e⟩
  obtain ⟨ρ, hρ, hρe⟩ := (hC1iii k r z z' γ hstd hpos).1.surjOn hmemT
  have hρu : C2.uMap k r z ρ = uρ := congrArg Prod.fst hρe
  have hρS := hRS ρ hρ
  have hρu' : IsUnit ρ.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hρS)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ρ⁻¹ * s := ⟨_, rfl⟩
  have hσS : σ ∈ Sset k r z := by rw [hσ]; exact hSg.2.1 _ (hSg.2.2 _ hρS) _ hs
  have hσu : C2.uMap k r z σ = v := by
    rw [hσ, (hU.1 _ (hSg.2.2 _ hρS)).2.2 s hs, huinv ρ hρS, hρu, hue, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (C2x2.ut_unit huρ), Matrix.one_mul]
  obtain ⟨h1, hh1, n1, hn1, hσe⟩ := hσS
  have hh1S := UW_sub_S hh1
  have hn1S := N_sub_S (z := z) hn1
  have hn1u : C2.uMap k r z n1 = v := by
    rw [← hσu, hσe, (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1, Matrix.one_mul]
  have hh1inv := WeylGroupFacts.uw_inv hh1
  have hh1u : IsUnit h1.det := WeylGroupFacts.isUnit_of_uh hh1.1
  have hn2 : h1 * n1 * h1⁻¹ ∈ Nset k r := (unitary_weyl_normal_holds k r z hz.1 h1 hh1 n1 hn1).1
  have hn2u : C2.uMap k r z (h1 * n1 * h1⁻¹) = v := by
    rw [(hU.1 _ (hSg.2.1 _ hh1S _ hn1S)).2.2 _ (UW_sub_S hh1inv), (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1,
      hU.2 _ hh1inv, hn1u, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
  obtain ⟨τv, hτv⟩ : ∃ τv, τv = C2.tauM k r z v := ⟨_, rfl⟩
  rw [← hτv] at hτN hτu
  have hτS : τv ∈ Sset k r z := N_sub_S hτN
  have hτunit : IsUnit τv.det := WeylGroupFacts.isUnit_of_uh hτN.1
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = h1 * n1 * h1⁻¹ * τv⁻¹ := ⟨_, rfl⟩
  have hn0N : n0 ∈ Nset k r := by rw [hn0]; exact hNg.2.1 _ hn2 _ (hNg.2.2 _ hτN)
  have hn0u : C2.uMap k r z n0 = 1 := by
    rw [hn0, (hU.1 _ (N_sub_S hn2)).2.2 _ (hSg.2.2 _ hτS), huinv _ hτS, hn2u, hτu,
      Matrix.mul_nonsing_inv _ (C2x2.ut_unit hv)]
  have hσdec : σ = n0 * τv * h1 := by
    rw [hσe, hn0, Matrix.mul_assoc (h1 * n1 * h1⁻¹), Matrix.nonsing_inv_mul _ hτunit, Matrix.mul_one,
      Matrix.mul_assoc (h1 * n1), Matrix.nonsing_inv_mul _ hh1u, Matrix.mul_one]
  have hσSg : σ ∈ C2.Sg k r z z' γ := ⟨n0, ⟨hn0N, hn0u⟩, v, hv, hvL, h1, hh1, by rw [hσdec, hτv]⟩
  refine ⟨(ρ, σ), ⟨hρ, hσSg, ?_⟩, ?_⟩
  · show s = ρ * σ
    rw [hσ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρu', Matrix.one_mul]
  · rintro ⟨ρ', σ'⟩ ⟨hρ', hσ', hse⟩
    simp only at hρ' hσ' hse
    obtain ⟨hσ'S, v', hv', hv'L, hσ'u⟩ := huSg σ' hσ'
    obtain ⟨hρ'U, hρ'L⟩ := hRimg ρ' hρ'
    have hus' : C2.uMap k r z s = C2.uMap k r z ρ' * v' := by
      rw [hse, (hU.1 _ (hRS ρ' hρ')).2.2 _ hσ'S, hσ'u]
    have := huniq (C2.uMap k r z ρ', v') ⟨hρ'U, hv', hρ'L, hv'L, hus'⟩
    rw [Prod.ext_iff] at this
    simp only at this
    have hρρ : ρ' = ρ := (hC1iii k r z z' γ hstd hpos).2.1 hρ' hρ (this.1.trans hρu.symm)
    subst hρρ
    have hρ'u : IsUnit ρ'.det := hρu'
    have : σ' = ρ'⁻¹ * s := by
      rw [hse, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ'u, Matrix.one_mul]
    rw [this, hσ]

end Formalism.FourierDecayAlt.P
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_trace {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (u v : Fin (2 * r + k + 1) → ℂ)
    (h1 : (Matrix.trace (ζ * Xuv k r u v)).re = 0)
    (h2 : (Matrix.trace (ζ * Xuv k r u (Complex.I • v))).re = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  rw [trace_xuv] at h1 h2
  have hs : ∀ w, herm (Hpk k r) (ζ *ᵥ w) u = -star (herm (Hpk k r) (ζ *ᵥ u) w) := by
    intro w
    rw [herm_skew hζ, herm_swap w]
  rw [hs] at h1 h2
  rw [herm_smul_right] at h2
  set A := herm (Hpk k r) (ζ *ᵥ u) v
  simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
  constructor <;> linarith

theorem herm_bvec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) x (bvec i) = (Hpk k r *ᵥ x) i := by
  rw [herm_eq, Finset.sum_eq_single i]
  · simp [bvec]
  · intro j _ hj; simp [bvec, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem herm_e (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (eI k r b)) = x (esI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inl (by simp [eI]))]
  rfl

theorem herm_es (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (esI k r b)) = x (eI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inr (by simp [esI]; omega))]
  congr 1
  apply Fin.ext
  simp [eI, esI]
  omega

theorem herm_w (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    herm (Hpk k r) x (bvec i) = if i.val = r + k then -x i else x i := by
  rw [herm_bvec, hpk_mulVec, if_neg (by omega)]

theorem inWb_sub {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (hv : inWb k r v) : inWb k r (u - v) := by
  intro i hi; simp [hu i hi, hv i hi]

theorem inWb_smul (c : ℂ) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (c • u) := by
  intro i hi; simp [hu i hi]

def sg (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_mulVec_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) i = sg (k := k) (r := r) i * u i := by
  rw [hpk_mulVec, sg]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hu i h, hu ⟨2 * r + k - i.val, by omega⟩ (by simp; omega), mul_zero]
  · rw [if_neg h]
    split_ifs <;> ring

def KI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

theorem herm_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u y = ∑ i ∈ Finset.univ.erase (KI k r), star (y i) * u i - star (y (KI k r)) * u (KI k r) := by
  rw [herm_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (KI k r))]
  have hK : sg (k := k) (r := r) (KI k r) = -1 := by simp [sg, KI]
  rw [hpk_mulVec_wb hu, hK]
  have : ∀ i ∈ Finset.univ.erase (KI k r), star (y i) * (Hpk k r *ᵥ u) i = star (y i) * u i := by
    intro i hi
    rw [hpk_mulVec_wb hu]
    have : i.val ≠ r + k := fun e => (Finset.mem_erase.1 hi).1 (Fin.ext (by simp [KI, e]))
    simp [sg, this]
  rw [Finset.sum_congr rfl this]
  ring

theorem re_star_mul_self (a : ℂ) : (star a * a).re = ‖a‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem wb_definite {z w : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hw : inWb k r w) (hwz : herm (Hpk k r) w z = 0) (hww : (herm (Hpk k r) w w).re ≤ 0) : w = 0 := by
  set S := Finset.univ.erase (KI k r)
  set K := KI k r
  have e2 : (herm (Hpk k r) w w).re = ∑ i ∈ S, ‖w i‖ ^ 2 - ‖w K‖ ^ 2 := by
    rw [herm_wb hw, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    rfl
  have eT : Tz k r z = ‖z K‖ ^ 2 - ∑ i ∈ S, ‖z i‖ ^ 2 := by
    rw [Tz, herm_wb hz, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    ring
  rw [herm_wb hw, sub_eq_zero] at hwz
  have hn : ‖z K‖ * ‖w K‖ ≤ ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by
    calc ‖z K‖ * ‖w K‖ = ‖star (z K) * w K‖ := by rw [norm_mul, norm_star]
      _ = ‖∑ i ∈ S, star (z i) * w i‖ := by rw [hwz]
      _ ≤ ∑ i ∈ S, ‖star (z i) * w i‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by simp only [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖z i‖) (fun i => ‖w i‖)
  set P := ∑ i ∈ S, ‖w i‖ ^ 2
  set Q := ∑ i ∈ S, ‖z i‖ ^ 2
  set m := ∑ i ∈ S, ‖z i‖ * ‖w i‖
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => by positivity)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => by positivity)
  have ha : 0 ≤ ‖w K‖ := norm_nonneg _
  have h1 : P ≤ ‖w K‖ ^ 2 := by linarith
  have h3 : (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := by
    have : 0 ≤ ‖z K‖ * ‖w K‖ := by positivity
    exact pow_le_pow_left₀ this hn 2
  have h4 : (‖z K‖ * ‖w K‖) ^ 2 ≤ Q * ‖w K‖ ^ 2 := by
    calc (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := h3
      _ ≤ Q * P := hcs
      _ ≤ Q * ‖w K‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hQ
  have h6 : ‖w K‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) := mul_pos hcon (by linarith)
    linarith
  have hwK : w K = 0 := by
    have : ‖w K‖ = 0 := by nlinarith
    exact norm_eq_zero.1 this
  have hP0 : P = 0 := le_antisymm (by nlinarith) hP
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hP0
  funext i
  by_cases hi : i = K
  · rw [hi, hwK]; rfl
  · have := hall i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
    rw [this]; rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def Hh (Y : Finset H) (κ : H → H → ℂ) (hat : Fin f → ℂ → H → H → ℂ) (σ : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, hat v (σ v) h h'

theorem eventually_norm_gt (v : Fin f) (a : ℝ) : ∀ᶠ x in crystallineComparison.atInfAll f, a < ‖x v‖ := by
  have h : ∀ᶠ x in Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop, a < ‖x v‖ :=
    (Filter.eventually_gt_atTop a).comap _
  unfold crystallineComparison.atInfAll
  exact Filter.mem_iInf_of_mem v h

theorem eventually_good (σ : crystallineComparison.V f) : ∀ᶠ x in crystallineComparison.atInfAll f, Good x ∧ Good (x + σ) := by
  have h1 : ∀ v, ∀ᶠ x in crystallineComparison.atInfAll f, x v ≠ 0 ∧ x v + σ v ≠ 0 := by
    intro v
    filter_upwards [eventually_norm_gt v ‖σ v‖] with x hx
    constructor
    · intro h
      rw [h, norm_zero] at hx
      exact absurd hx (not_lt.mpr (norm_nonneg _))
    · intro h
      have e : x v = -σ v := eq_neg_of_add_eq_zero_left h
      rw [e, norm_neg] at hx
      exact lt_irrefl _ hx
  filter_upwards [Filter.eventually_all.mpr h1] with x hx
  exact ⟨fun v => (hx v).1, fun v => (hx v).2⟩

theorem tendsto_coord (v : Fin f) : Tendsto (fun x : crystallineComparison.V f => x v) (crystallineComparison.atInfAll f) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, Filter.tendsto_comap_iff]
  exact Filter.tendsto_comap.mono_left (iInf_le (fun v => Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop) v)

theorem phiG_tendsto (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => K v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => phiG Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => phi Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    rw [phiG, if_pos hx]
  · unfold phi Hh
    refine tendsto_finsetSum _ (fun h hh => tendsto_finsetSum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finsetProd _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

theorem phiG_conj_tendsto (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => conj (K v (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => conj (phiG Y κ K (x + σ) x)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  have hherm : ∀ h ∈ Y, ∀ h' ∈ Y, conj (κ h' h) = κ h h' := by
    intro h hh h' hh'
    have := hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩
    simp only [Matrix.of_apply] at this
    exact this
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (K v (h', x v + σ v) (h, x v)))
    (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    symm
    rw [phiG, if_pos ⟨hx.2, hx.1⟩, phi]

    simp only [map_sum, map_mul, map_prod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun h' hh' => ?_))
    rw [hherm h hh h' hh']
    rfl
  · unfold Hh
    refine tendsto_finsetSum _ (fun h hh => tendsto_finsetSum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finsetProd _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

section mean

variable (Λ : AddSubgroup (crystallineComparison.V f)) (LIM : (Λ → ℂ) → ℂ)

end mean

end

end Formalism.FourierDecayAlt.P.PBC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def RadDZ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∃ (n : ℕ) (A : (j : ℕ) → ℂ →
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp))),
    (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j)
      {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}) ∧
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        ∑ j ∈ Finset.range (n + 1), A j q.2
          (iteratedFDeriv ℝ j (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2)

end preds

def GTCLRadT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b)

def GTCLNab : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → (∀ (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b)) →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      RadDZ P Bs d.L.nab.1 ∧ RadDZ P Bs d.L.nabs.1

def GTCLFrame : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      RadDZ P Bs d.L.nab.1 → RadDZ P Bs d.L.nabs.1 →
      ∃ A B : M.Ty P → ℂ → ℂ, SmAB P A B ∧ ConnF P Bs d e A B

def GTCLocalOfCut : Prop := GTCLRadT → GTCLNab → GTCLFrame → GTCLocal

theorem gTCLocal_of_cut : GTCLocalOfCut := by
  intro hT hN hF Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk
  have hRT := hT Wp Wq P Bs hH.1 hH.2.1 hH.2.2.1 X
  obtain ⟨h1, h2⟩ := hN Wp Wq P Bs X d hH hRT e he hk
  exact hF Wp Wq P Bs X d hH e he hk h1 h2

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem annulus_condition_holds : GTCAnnulus := by
  intro TT α hTT hα hcurv hper
  have hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n :=
    hper (TT + 1) (by linarith) (by nlinarith [sq_nonneg (TT + 1 / 2)])
  have hcurv' : ∀ ζ : ℂ, TT < Complex.normSq ζ → (Ann.wZb α ζ).re = 0 := hcurv
  refine ⟨Ann.uu TT α, Ann.contDiffOn_uu hTT hα hcurv' hhol, fun ζ hζ => ?_⟩
  obtain ⟨h1, h2⟩ := Ann.wZ_uu hTT hα hcurv' hhol (ζ := ζ) hζ
  have hn : ‖Ann.uu TT α ζ‖ = 1 := Ann.norm_uu ζ
  have hs : star (Ann.uu TT α ζ) * Ann.uu TT α ζ = 1 := by
    calc star (Ann.uu TT α ζ) * Ann.uu TT α ζ
        = (starRingEnd ℂ) (Ann.uu TT α ζ) * Ann.uu TT α ζ := rfl
      _ = ((‖Ann.uu TT α ζ‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      _ = 1 := by rw [hn]; norm_num
  refine ⟨hn, ?_, ?_⟩
  · show star (Ann.uu TT α ζ) * Ann.wZ (Ann.uu TT α) ζ = α ζ
    rw [h1, ← mul_assoc, hs, one_mul]
  · show star (Ann.uu TT α ζ) * Ann.wZb (Ann.uu TT α) ζ = -star (α ζ)
    rw [h2, mul_neg, ← mul_assoc, hs, one_mul] <;> rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
