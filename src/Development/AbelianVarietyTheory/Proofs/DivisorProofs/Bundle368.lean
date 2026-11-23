module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle046
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.SUVol
open Matrix

namespace GlobalTheory.SUVol

theorem ncard_image_lifts_eq_card_specialUnitaryGroup {O : Type*} [CommRing O] (w : Ideal O)
    [StarRing (O ⧸ w)] (c : O → O)
    (hc : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x)) (r : ℕ) :
    Set.ncard ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Nat.card (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w)) := by
  have key : ∀ g : Matrix (Fin r) (Fin r) O,
      (g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w) ↔
        (g.map (Ideal.Quotient.mk w))ᵀ ∈ Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) := by
    intro g
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.det_transpose,
      and_comm]
    refine and_congr ?_ ?_
    · rw [← Matrix.ext_iff]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]
      have e1 : Ideal.Quotient.mk w ((gᵀ * g.map c) a b) =
          ((g.map (Ideal.Quotient.mk w))ᵀ * star (g.map (Ideal.Quotient.mk w))ᵀ) a b := by
        simp [Matrix.mul_apply, Matrix.star_apply, hc]
      have e2 : Ideal.Quotient.mk w ((1 : Matrix (Fin r) (Fin r) O) a b) =
          (1 : Matrix (Fin r) (Fin r) (O ⧸ w)) a b := by
        simp only [Matrix.one_apply]; split_ifs <;> simp
      rw [e1, e2]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_one, RingHom.map_det,
        RingHom.mapMatrix_apply]
  have himg : ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Matrix.transpose '' (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) : Set _) := by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, (key g).1 hg, Matrix.transpose_transpose _⟩
    · rintro ⟨B, hB, rfl⟩
      choose s hs using Ideal.Quotient.mk_surjective (I := w)
      have e : (Bᵀ.map s).map (Ideal.Quotient.mk w) = Bᵀ := by
        ext a b; simp [hs]
      refine ⟨Bᵀ.map s, (key _).2 ?_, e⟩
      rw [e, Matrix.transpose_transpose]; exact hB
  rw [himg, Set.ncard_image_of_injective _ Matrix.transpose_injective, ← Nat.card_coe_set_eq]
  rfl

theorem exists_star_ne_of_not_surjective {K A : Type*} [Field K] [Finite K] [StarRing K]
    (f : A → K) (hadd : ∀ x : K, ∃ a, f a = x + star x) (hmul : ∀ x : K, ∃ a, f a = x * star x)
    (hf : ¬ Function.Surjective f) : ∃ a : K, star a ≠ a := by
  by_contra h
  push Not at h
  apply hf
  intro x
  by_cases h2 : (2 : K) = 0
  · have hinj : Function.Injective (fun y : K => y * y) := by
      intro y z hyz
      simp only at hyz
      have : (y - z) * (y - z) = 0 := by linear_combination hyz + (z * z - y * z) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj x
    obtain ⟨a, ha⟩ := hmul y
    exact ⟨a, by rw [ha, h y]; exact hy⟩
  · obtain ⟨a, ha⟩ := hadd (x / 2)
    exact ⟨a, by rw [ha, h]; field_simp; ring⟩

theorem prod_le_locFactor_of_isPrime (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r)
    (hw : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime) :
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  classical
  unfold locFactor resOrder
  rw [if_pos hw]
  set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef
  set c := IsCMField.ringOfIntegersComplexConj E with hcdef
  have hcc : ∀ x, c (c x) = x := fun x => by
    ext; simp [hcdef]
  have hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a :=
    fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩
  have hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E) := by
    rw [hwdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c _ ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  have hw0 : w ≠ ⊥ := by
    rw [hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  haveI hmax : w.IsMaximal := hw.isMaximal hw0
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  let σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w) := Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle
  have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := fun x => rfl
  letI : StarRing (𝓞 E ⧸ w) :=
    { star := σ
      star_involutive := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change σ (σ _) = _
        rw [hσ, hσ, hcc]
      star_mul := fun x y => by
        change σ (x * y) = σ y * σ x
        rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := hσ
  rw [ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]
  set q := Ideal.absNorm v.asIdeal with hq
  have hK : Nat.card (𝓞 E ⧸ w) = q ^ 2 := by
    have h := Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal
    rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _),
      Submodule.cardQuot_apply] at h
    exact h
  have hq2 : 2 ≤ q := GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK
  have hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a := by
    let f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w) :=
      Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map
    have hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a) :=
      fun a => rfl
    refine exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1
        (by change c _ = _; rw [map_add (f := _), hcc, add_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add (f := _)]⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1
        (by change c _ = _; rw [map_mul, hcc, mul_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩
    · haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
      have h1 := Nat.card_le_card_of_surjective f hsurj
      have h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q := by
        rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hK, h2] at h1
      nlinarith
  have h := GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  rw [le_div_iff₀ (by positivity)]
  refine le_of_le_of_eq ?_ h'.symm
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_))
    (by positivity)
  · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hq1))
  · have hp : (0 : ℝ) ≤ ((q : ℝ) ^ i)⁻¹ := by positivity
    rcases neg_one_pow_eq_or ℝ i with h1 | h1 <;> rw [h1] <;> linarith

end GlobalTheory.SUVol
end

section

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.PhaseLipschitz

def psi (k : ℝ) : ℝ → ℂ := fun t =>
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) - 1

theorem eChar_sub_one_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (k : ℝ) :
    (fun y => eChar (L y + k) - 1) = psi k ∘ ⇑L := by
  funext y
  simp only [psi, Function.comp_apply, eChar_apply, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem contDiff_psi (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi k) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold psi; fun_prop

theorem norm_psi_le (k t : ℝ) : ‖psi k t‖ ≤ 2 * Real.pi * |t + k| := by
  have e : psi k t = Complex.exp (Complex.I * ((2 * Real.pi * (t + k) : ℝ) : ℂ)) - 1 := by
    simp only [psi, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

theorem iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (psi k) = fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * (2 * Real.pi * Complex.I) ^ (j + 1) *
        Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  rw [iteratedDeriv_succ']
  have hd : deriv (psi k) = deriv (fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) := by
    unfold psi; exact deriv_sub_const_fun _
  rw [hd, ← iteratedDeriv_succ', GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp]

theorem norm_iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv (j + 1) (psi k) t‖ = (2 * Real.pi) ^ (j + 1) := by
  rw [iteratedDeriv_psi_succ]
  have h1 : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  simp only [norm_mul, norm_pow, h1]
  simp [abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_psi_comp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) {N i : ℕ} (hi : i ≤ N) (x : V) :
    ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ ≤
      (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * (1 + ‖x‖) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL := norm_nonneg L
  have hx := norm_nonneg x
  have hk := abs_nonneg k
  have h1N : (1 : ℝ) ≤ (1 + ‖L‖) ^ N := one_le_pow₀ (by linarith)
  rcases i with _ | j
  · rw [norm_iteratedFDeriv_zero, Function.comp_apply]
    refine (norm_psi_le k (L x)).trans ?_
    have h2 : |L x + k| ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by
      have h3 : |L x| ≤ ‖L‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using L.le_opNorm x
      calc |L x + k| ≤ |L x| + |k| := abs_add_le _ _
        _ ≤ ‖L‖ * ‖x‖ + |k| := by linarith
        _ ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by nlinarith
    have h4 : 2 * Real.pi ≤ (2 * Real.pi) ^ (N + 1) := le_self_pow₀ hpi (by omega)
    calc 2 * Real.pi * |L x + k| ≤ 2 * Real.pi * ((‖L‖ + |k|) * (1 + ‖x‖)) := by gcongr
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * 1) * (1 + ‖x‖) := by
          rw [mul_one]; rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr
  · rw [L.iteratedFDeriv_comp_right (contDiff_psi k) x (i := j + 1) (by exact_mod_cast le_top)]
    have h5 : (2 * Real.pi) ^ (j + 1) ≤ (2 * Real.pi) ^ (N + 1) := pow_le_pow_right₀ hpi (by omega)
    have h6 : ‖L‖ ^ (j + 1) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by
      rw [pow_succ']
      gcongr
      · linarith
      · calc ‖L‖ ^ j ≤ (1 + ‖L‖) ^ j := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ N := pow_le_pow_right₀ (by linarith) (by omega)
    calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (psi k) (L x)‖ * ∏ _j : Fin (j + 1), ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = (2 * Real.pi) ^ (j + 1) * ‖L‖ ^ (j + 1) := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_psi_succ]; simp
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * 1 := by
          rw [mul_one]; gcongr
      _ ≤ _ := by gcongr; linarith

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) : Function.HasTemperateGrowth (fun y => eChar (L y + k)) :=
  hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))

theorem coe_smulLeft_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    ⇑(SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) = fun y => (psi k ∘ ⇑L) y * f y := by
  funext y
  rw [SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L k), smul_eq_mul,
    ← congrFun (eChar_sub_one_eq L k) y]
  ring

theorem seminorm_smulLeft_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A N a n : ℕ} (ha : a ≤ A) (hn : n ≤ N) (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ a n (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤
      ((N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1)) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) *
        (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  set S := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hS
  set P := (‖L‖ + |k|) * (1 + ‖L‖) ^ N with hP
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hP0 : 0 ≤ P := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ a n _ (by positivity) fun x => ?_
  rw [coe_smulLeft_sub]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_psi k).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx := norm_nonneg x
  have hf : ∀ j ≤ N, ‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ 2 ^ (A + 1) * S := by
    intro j hj
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (A + 1, N)) (k := a + 1) (n := j)
      (by simp; omega) hj f x
    have h' : ‖x‖ ^ a * (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (a + 1) := by
      rw [pow_succ]; gcongr; linarith
    calc _ ≤ (1 + ‖x‖) ^ (a + 1) * ‖iteratedFDeriv ℝ j f x‖ := by gcongr
      _ ≤ _ := h
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_psi_comp_le L k (N := N) (i := i) (by omega) x
    have h2 := hf (n - i) (by omega)
    have hc : (n.choose i : ℝ) ≤ 2 ^ N :=
      (by exact_mod_cast Nat.choose_le_two_pow n i : (n.choose i : ℝ) ≤ 2 ^ n).trans
        (pow_le_pow_right₀ (by norm_num) hn)
    calc ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        ≤ ‖x‖ ^ a * ((2 ^ N : ℝ) * ((2 * Real.pi) ^ (N + 1) * P * (1 + ‖x‖)) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) *
          (‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ _ := by gcongr
  calc ‖x‖ ^ a * ‖iteratedFDeriv ℝ n (fun y => (psi k ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ a * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ a * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by simp
    _ ≤ ((N : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by
        gcongr
    _ = _ := by ring

theorem continuous_finset_sup_seminorm {E ι : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {p : ι → Seminorm ℂ E} (hp : ∀ i, Continuous (p i)) (s : Finset ι) :
    Continuous ⇑(s.sup p : Seminorm ℂ E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact ((hp i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm

theorem seminorm_smulLeft_eChar_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
      p (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f) ≤
        (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set A := s.sup Prod.fst with hA
  set N := s.sup Prod.snd with hN
  set K : ℝ := (N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set Q : Seminorm ℂ (SchwartzMap V ℂ) :=
    (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) with hQ
  refine ⟨(C * ⟨K, hK0⟩ : NNReal) • Q, N, ?_, ?_⟩
  · exact (continuous_finset_sup_seminorm
      (fun i => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i) _).const_smul _
  · intro L k f
    set g := SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f
    have hP0 : 0 ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by positivity
    have hQ0 : 0 ≤ Q f := apply_nonneg _ _
    have hs : (s.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      exact seminorm_smulLeft_sub_le (Finset.le_sup (f := Prod.fst) hi) (Finset.le_sup (f := Prod.snd) hi) L k f
    calc p g ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) g := hC g
      _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) g := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
      _ ≤ (C : ℝ) * (K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f) := by gcongr
      _ = (‖L‖ + |k|) * (1 + ‖L‖) ^ N * (((C * ⟨K, hK0⟩ : NNReal) • Q) f) := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
          change (C : ℝ) * _ = _ * (((C : ℝ) * K) * Q f)
          ring

end GlobalTheory.PhaseLipschitz
end
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.Proof.schrodinger_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  intro l _ _ w φ f f₁ hf hf₁
  obtain ⟨p, q⟩ := w
  have h : ⇑f₁ = rhoFun (Sum.elim p q) ⇑f := by
    funext x
    rw [hf₁, GlobalTheory.Published.Metaplectic.rho_apply, rhoFun, hf]
    simp only [phase, pPart, qPart, Sum.elim_inl, Sum.elim_inr, PiLp.inner_apply, WithLp.ofLp_add]
    congr 1
    · congr 1
      push_cast
      simp only [dotProduct, RCLike.inner_apply, conj_trivial, Finset.sum_div]
      push_cast
      ring_nf
      rw [Finset.sum_congr rfl fun i _ => mul_comm ((q i : ℝ) : ℂ) ((p i : ℝ) : ℂ)]
      ring
  refine Lp.ext ((f₁.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho _ _).trans (rhoFun_congr _ (f.coeFn_toLp 2 volume))).symm
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory
namespace MatrixCoeff

theorem norm_le_max_parts (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) : ‖w‖ ≤ max ‖pPart w‖ ‖qPart w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rcases i with j | j
  · exact le_max_of_le_left (by
      have := PiLp.norm_apply_le (pPart w) j
      simpa [pPart] using this)
  · exact le_max_of_le_right (by
      have := PiLp.norm_apply_le (qPart w) j
      simpa [qPart] using this)

theorem one_add_norm_pow_le_parts (n N : ℕ) (w : Fin n ⊕ Fin n → ℝ) :
    (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N := by
  have h := norm_le_max_parts n w
  rcases le_total ‖pPart w‖ ‖qPart w‖ with h' | h'
  · rw [max_eq_right h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖qPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖pPart w‖) N]
  · rw [max_eq_left h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖qPart w‖) N]

end MatrixCoeff

open MatrixCoeff

theorem matrixCoeff_continuous_rapidDecay : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by
  intro n g g'
  refine ⟨GlobalTheory.T.continuous_matrix_coefficient n g g', fun N => ?_⟩
  obtain ⟨C1, h1⟩ := GlobalTheory.T.matrix_coeff_decay_first_part n g g' N
  obtain ⟨C2, h2⟩ := GlobalTheory.T.matrix_coeff_decay_second_part n g g' N
  refine ⟨C1 + C2, fun w => ?_⟩
  have := one_add_norm_pow_le_parts n N w
  have hn : 0 ≤ ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ := norm_nonneg _
  calc _ ≤ ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * ((1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N) :=
        mul_le_mul_of_nonneg_left this hn
    _ ≤ C1 + C2 := by rw [mul_add]; exact add_le_add (h1 w) (h2 w)

end GlobalTheory
end
