module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

theorem map_cT_of_conj {E : Type} [Field E] (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x))
    {a b : Type} (M : Matrix a b E) : (cT σ M).map τ = (M.map τ)ᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, hτ]

theorem gM_mem_Nset (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ w, gM A γ w ∈ Nset k r := by
  intro hV γ hγ w
  obtain ⟨hCM, -, hJ, -, -, hD, -, hM, hs, hAd⟩ := hV
  obtain ⟨⟨hU, ⟨ν, hν, hγe⟩, hX⟩, -⟩ := hγ
  set τ := w.embedding with hτdef
  have hτ : ∀ x, τ ((σ : E →+* E) x) = star (τ x) := fun x => hCM.2.2.2 τ x
  set B := A w with hBdef
  set G := γ.map τ with hGdef
  set H := Hpk k r with hHdef
  set Ew := (eOf P).map τ with hEwdef
  have hJw : Bᴴ * H * B = J.map τ := hM w

  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hJw
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    have h2 : τ J.det = (J.map τ).det := by rw [RingHom.map_det]; rfl
    exact hJ.2 ((map_eq_zero τ).1 (h2.trans h1.symm))
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hBiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu

  have hGU : Gᴴ * J.map τ * G = J.map τ := by
    have h1 := congrArg (fun M => M.map τ) hU
    simp only [IsUn, Matrix.map_mul, map_cT_of_conj _ τ hτ] at h1
    exact h1

  set S : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => (s a : ℂ) * bvec (eI k r a) i with hSdef
  have hAE : B * Ew = S := by
    ext i a
    have h1 := congrFun (hAd w a).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ew, eOf, S] using h1
  have hgM : gM A γ w = B * G * B⁻¹ := rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    show (gM A γ w)ᴴ * H * gM A γ w = H
    rw [hgM]
    calc (B * G * B⁻¹)ᴴ * H * (B * G * B⁻¹) = (B⁻¹)ᴴ * (Gᴴ * (Bᴴ * H * B) * G) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * H * B) * B⁻¹ := by rw [hJw, hGU]
      _ = (B * B⁻¹)ᴴ * H * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hBB]; simp
  ·
    have hGE : G * Ew = Ew * ν.map τ := by
      show γ.map τ * (eOf P).map τ = (eOf P).map τ * ν.map τ
      rw [← Matrix.map_mul, ← Matrix.map_mul, hγe]
      rfl
    have hgS : gM A γ w * S = S * ν.map τ := by
      rw [hgM, ← hAE]
      calc B * G * B⁻¹ * (B * Ew) = B * G * (B⁻¹ * B) * Ew := by simp only [Matrix.mul_assoc]
        _ = B * (G * Ew) := by rw [hBiB, Matrix.mul_one, Matrix.mul_assoc]
        _ = B * Ew * ν.map τ := by rw [hGE, Matrix.mul_assoc]
    intro b i hbi
    have h1 := congrFun (congrFun hgS i) b
    have hl : (gM A γ w * S) i b = gM A γ w i (eI k r b) * (s b : ℂ) := by
      simp [S, Matrix.mul_apply, bvec, Pi.single_apply]
    have hr : (S * ν.map τ) i b = (s b : ℂ) * (if i = eI k r b then 1 else 0) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · simp [S, bvec, Pi.single_apply, (hν b b).2 rfl]
      · intro a _ hab
        by_cases hia : i = eI k r a
        · have hba : b < a := by
            have : b.val ≤ a.val := by rw [hia] at hbi; exact hbi
            exact lt_of_le_of_ne this (fun h => hab h.symm)
          simp [(hν a b).1 hba]
        · simp [S, bvec, Pi.single_apply, hia]
      · simp
    rw [hl, hr] at h1
    have hs0 : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have h2 := mul_right_cancel₀ hs0 (h1.trans (mul_comm _ _))
    exact h2
  ·
    have hH : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)), r ≤ j.val → j.val ≤ r + k → H (eI k r a) j = 0 := by
      intro a j h1 h2
      have ha := a.isLt
      have hv : (eI k r a).val = a.val := rfl
      show Hpk k r (eI k r a) j = 0
      unfold Hpk
      rw [if_neg (by rw [hv]; omega), if_neg (by omega), if_neg (fun h => absurd h.1 (by rw [hv]; omega))]
    set K := cT (σ : E →+* E) (eOf P) * J with hKdef
    have hKf : K * f = 1 := by
      ext a b
      have h1 := congrFun (congrFun hD.1 a.castSucc) b
      simp only [pairM, K, cT, eOf, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
        Matrix.submatrix_apply, id, Matrix.of_apply, Matrix.one_apply] at h1 ⊢
      rw [h1]
      simp [Fin.castSucc_inj]
    set Q := 1 - f * K with hQdef
    have hKQ : K * Q = 0 := by
      rw [hQdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKf, Matrix.one_mul, sub_self]
    have hcol : ∀ j, ∃ c, γ *ᵥ (Q *ᵥ Pi.single j 1) - Q *ᵥ Pi.single j 1 = eOf P *ᵥ c := by
      intro j
      apply hX
      rw [Matrix.mulVec_mulVec, hKQ, Matrix.zero_mulVec]
    choose c hc using hcol
    set C : Matrix (Fin r) (Fin (2 * r + k + 1)) E := Matrix.of fun a j => c j a with hCdef
    have hsj : ∀ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) i j, (M *ᵥ Pi.single j 1) i = M i j := by
      intro M i j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hQC : (γ - 1) * Q = eOf P * C := by
      ext i j
      have h1 := congrFun (hc j) i
      rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec] at h1
      have e1 : γ * Q - Q = (γ - 1) * Q := by rw [Matrix.sub_mul, Matrix.one_mul]
      rw [e1, hsj] at h1
      rw [h1, Matrix.mul_apply]
      simp [Matrix.mulVec, dotProduct, C]
    set fw := f.map τ with hfwdef
    set Kw := Ewᴴ * J.map τ with hKwdef
    have hQw : (G - 1) * (1 - fw * Kw) = Ew * C.map τ := by
      have h1 := congrArg τ.mapMatrix hQC
      rw [map_mul, map_sub, map_one, hQdef, map_sub, map_one] at h1
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul, hKdef, map_cT_of_conj _ τ hτ] at h1
      exact h1
    have hKB : Kw * B⁻¹ = Sᴴ * H := by
      show Ewᴴ * J.map τ * B⁻¹ = Sᴴ * H
      rw [← hJw, ← hAE]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hBB, Matrix.mul_one]
    have hdecomp : gM A γ w - 1 = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
      have e1 : gM A γ w - 1 = B * (G - 1) * B⁻¹ := by
        rw [hgM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBB]
      rw [e1]
      calc B * (G - 1) * B⁻¹ = B * (G - 1) * ((1 - fw * Kw) + fw * Kw) * B⁻¹ := by
            rw [sub_add_cancel, Matrix.mul_one]
        _ = B * ((G - 1) * (1 - fw * Kw)) * B⁻¹ + B * (G - 1) * fw * (Kw * B⁻¹) := by
            rw [Matrix.mul_add, Matrix.add_mul]; simp only [Matrix.mul_assoc]
        _ = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
            rw [hQw, hKB, ← hAE]; simp only [Matrix.mul_assoc]
    intro i j hj1 hj2 hi
    have h1 := congrFun (congrFun hdecomp i) j
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply] at h1
    have z1 : (S * (C.map τ * B⁻¹)) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hia : i ≠ eI k r a := fun h => by
        have ha := a.isLt
        rw [h] at hi
        exact absurd hi (show ¬ r ≤ a.val by omega)
      simp [S, bvec, Pi.single_apply, hia]
    have z2 : (B * (G - 1) * fw * (Sᴴ * H) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have h3 : (Sᴴ * H : Matrix (Fin r) (Fin (2 * r + k + 1)) ℂ) a j = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l = eI k r a
        · subst hl
          rw [hH a j hj1 hj2, mul_zero]
        · simp [S, bvec, Pi.single_apply, hl, Matrix.conjTranspose_apply]
      rw [h3, mul_zero]
    rw [z1, z2, add_zero] at h1
    exact sub_eq_zero.1 h1

end GlobalTheory.SnMass.VolN

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.Covol

theorem sum_UTr_fst (r : ℕ) (u : Fin r → ℝ) :
    ∑ p : UTr r, u p.1.1 = ∑ a : Fin r, ((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => u x.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, ← Fin.card_Ioi]
  congr 3
  ext b; simp

theorem sum_UTr_snd (r : ℕ) (v : Fin r → ℝ) :
    ∑ p : UTr r, v p.1.2 = ∑ b : Fin r, ((b : ℕ) : ℝ) * v b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => v x.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Fin.card_Iio b]; congr 1; ext a; simp

theorem sum_UTr (r : ℕ) (u v : Fin r → ℝ) :
    ∑ p : UTr r, (u p.1.1 + v p.1.2) =
      ∑ a : Fin r, (((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a + ((a : ℕ) : ℝ) * v a) := by
  rw [Finset.sum_add_distrib, sum_UTr_fst, sum_UTr_snd, ← Finset.sum_add_distrib]

theorem sum_fin_quad (r : ℕ) (c₀ c₁ c₂ : ℝ) :
    ∑ a : Fin r, (c₀ + c₁ * ((a : ℕ) : ℝ) + c₂ * ((a : ℕ) : ℝ) ^ 2) =
      c₀ * r + c₁ * (r * (r - 1) / 2) + c₂ * ((r - 1) * r * (2 * r - 1) / 6) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => c₀ + c₁ * (i : ℝ) + c₂ * (i : ℝ) ^ 2) r]
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end GlobalTheory.SnMass.VolN.Covol

namespace GlobalTheory.SnMass.VolN


open Covol in
theorem covol_blocks_prod : ∀ (d : ℝ) (f k r : ℕ) (s : Fin r → ℝ), 0 < d → (∀ a, 0 < s a) → (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) * ((∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * f)) * (∏ a : Fin r, ((2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * f)) ^ (k + 1)) * (∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * f)) * ∏ a : Fin r, d ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ f) = d ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ f := by
  intro d f k r s hd hs
  obtain ⟨δ, rfl⟩ : ∃ δ, d = Real.exp δ := ⟨Real.log d, (Real.exp_log hd).symm⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin r → ℝ, s = fun a => Real.exp (σ a) :=
    ⟨fun a => Real.log (s a), funext fun a => (Real.exp_log (hs a)).symm⟩
  beta_reduce
  have h2i : (2⁻¹ : ℝ) = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log two_pos]
  have e1 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) +
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) / Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (2 * δ * ((r - p.1.2.val : ℕ) : ℝ) - 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
    congr 1; push_cast; ring
  have e3 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) -
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) * Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (-(2 * δ * ((r - p.1.2.val : ℕ) : ℝ)) + 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e2 : ∀ a : Fin r, ((2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) *
      Real.exp (σ a) ^ (2 * f)) ^ (k + 1) =
      Real.exp (((k : ℝ) + 1) * (-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)) := by
    intro a
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e4 : ∀ a : Fin r, Real.exp δ ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (Real.exp (σ a) ^ 2) ^ f =
      Real.exp (δ * (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a) := by
    intro a
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e5 : ∀ a : Fin r, Real.exp (σ a) ^ (4 * (r - (a : ℕ)) + 2 * k) =
      Real.exp (((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) * σ a) := fun a => (Real.exp_nat_mul _ _).symm
  rw [Finset.prod_congr rfl (fun p _ => e1 p), Finset.prod_congr rfl (fun a _ => e2 a),
    Finset.prod_congr rfl (fun p _ => e3 p), Finset.prod_congr rfl (fun a _ => e4 a),
    Finset.prod_congr rfl (fun a _ => e5 a)]
  have hu1 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => 2 * δ * ((r - b.val : ℕ) : ℝ) - 2 * f * σ b)
  have hu3 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => -(2 * δ * ((r - b.val : ℕ) : ℝ)) + 2 * f * σ b)
  beta_reduce at hu1 hu3
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, hu1, hu3]
  rw [show (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) =
      Real.exp (((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) * Real.log 2) by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]]
  simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
  rw [Real.exp_eq_exp]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← sub_eq_zero, show ∀ x y z w : ℝ, x + y - (z + w) = (y - w) + (x - z) from fun _ _ _ _ => by ring,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (g := fun a : Fin r =>
      (δ * (2 * ((r : ℝ) - 1) * (1 - 2 * r) + ((k : ℝ) + 1) * (1 - 2 * r) + 1 / 2 - 2 * r) -
        Real.log 2 * f * (2 * r + k - 1)) +
      (δ * (8 * r + 2 * k - 2) + 2 * f * Real.log 2) * ((a : ℕ) : ℝ) + (-4 * δ) * ((a : ℕ) : ℝ) ^ 2) ?hc,
    sum_fin_quad]
  · have hN : ((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) = f * (r * ((r : ℝ) - 1) + r * (k + 1)) := by
      rcases r with _ | n
      · simp
      · push_cast [Nat.add_sub_cancel]; ring
    rw [hN]; ring
  · intro a _
    have ha := a.isLt
    have h1 : ((r - (a : ℕ) : ℕ) : ℝ) = r - (a : ℕ) := by rw [Nat.cast_sub ha.le]
    have h2 : ((r - 1 - (a : ℕ) : ℕ) : ℝ) = r - 1 - (a : ℕ) := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : ((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) = 4 * ((r : ℝ) - (a : ℕ)) + 2 * k := by
      push_cast [Nat.cast_sub ha.le]; ring
    rw [h3, h2, h1]; ring

end GlobalTheory.SnMass.VolN
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.DepOne

theorem Hpk_mulVec_e {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have := a.isLt
    have h1 : (eI k r a).val = a.val := rfl
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    unfold Hpk
    rw [if_pos (by omega), one_mul]
  · intro l _ hl
    have hl' : l.val ≠ 2 * r + k - a.val := fun h => hl (Fin.ext h)
    have := a.isLt
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp

theorem Hpk_e_es {k r : ℕ} (a b : Fin r) :
    Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold Hpk
  by_cases hab : a = b
  · subst hab
    rw [if_pos (by omega), if_pos rfl]
  · have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hab]

theorem es_es {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r)
    (b : Fin r) : ∀ (n : ℕ) (a : Fin r), a.val = n → a ≤ b →
      x (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a han hab
  have hU : xᴴ * Hpk k r * x = Hpk k r := hx.1
  have h := congrFun (congrFun hU (eI k r a)) (esI k r b)
  rw [Matrix.mul_assoc, Hpk_e_es] at h
  have hs : (xᴴ * (Hpk k r * x)) (eI k r a) (esI k r b) =
      ∑ i, star (x i (eI k r a)) * (Hpk k r *ᵥ fun l => x l (esI k r b)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [hs, Finset.sum_eq_single (eI k r a)] at h
  · rw [Hpk_mulVec_e, hx.2.1 a (eI k r a) le_rfl, if_pos rfl, star_one, one_mul] at h
    exact h
  · intro i _ hi
    by_cases hia : a.val ≤ i.val
    · rw [hx.2.1 a i hia, if_neg hi, star_zero, zero_mul]
    · have ha := a.isLt
      obtain ⟨c, rfl⟩ : ∃ c : Fin r, i = eI k r c := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      have hca : c.val < a.val := by simpa [eI] using not_le.1 hia
      rw [Hpk_mulVec_e]
      have hcb : c ≤ b := le_trans (le_of_lt (show c < a from hca)) hab
      rw [ih c.val (han ▸ hca) c rfl hcb, if_neg (fun h => by
        subst h; exact absurd hab (not_le.2 hca)), mul_zero]
  · simp

theorem dep_one : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    x ∈ Nset k r → Dep k r 1 (x - 1) := by
  intro k r x hx i j hij
  rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  have hi := i.isLt
  have hj := j.isLt
  simp only [pos] at hij
  by_cases hjr : j.val < r
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have e : j = eI k r ⟨j.val, hjr⟩ := Fin.ext rfl
    have := hx.2.1 ⟨j.val, hjr⟩ i hji
    rw [← e] at this
    exact this
  by_cases hjm : j.val ≤ r + k
  · have hri : r ≤ i.val := by split_ifs at hij <;> omega
    exact hx.2.2 i j (by omega) hjm hri
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have hb : 2 * r + k - j.val < r := by omega
    have hc : 2 * r + k - i.val < r := by omega
    have ej : j = esI k r ⟨2 * r + k - j.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    have ei : i = esI k r ⟨2 * r + k - i.val, hc⟩ := Fin.ext (by simp [esI]; omega)
    have key := es_es hx ⟨2 * r + k - j.val, hb⟩ _ ⟨2 * r + k - i.val, hc⟩ rfl
      (by rw [Fin.mk_le_mk]; omega)
    rw [← ei, ← ej] at key
    rw [key]
    by_cases hij' : i = j
    · subst hij'; simp
    · rw [if_neg hij', if_neg]
      intro h
      apply hij'
      rw [ei, ej, h]

end GlobalTheory.SnMass.VolN.DepOne
end
end
