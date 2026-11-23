module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
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
public import Mathlib.NumberTheory.MulChar.Lemmas
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem coeff_fg : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω),
    InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε f h hf hh
  obtain ⟨N, w, hN, hLv⟩ := hf
  obtain ⟨b, hb, hbE⟩ := hLv.2 1
  have hb' : HasQ N (fun τ => DD τ ^ w * f τ) b := by
    simpa only [one_smul] using hb
  choose a ha using fun n => (hbE n : b n ∈ ε.range)
  have hb'' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) := by
    have : (fun n => ε (a n)) = b := funext ha
    rw [this]; exact hb'
  obtain ⟨S, hS⟩ := GlobalTheory.T.qExpansion_coeffs_mem_finitelyGenerated Ω ε N w f a hN hLv hb''
  obtain ⟨H, hH, hHa, hH0⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N (fun τ => DD τ ^ w * f τ) a hN hb''
  obtain ⟨hD, hDe, hD0, hDl, hDz⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hops, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨hmul, hinv⟩ := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω (Subring.closure (S : Set Ω))
  set A := Subring.closure (S : Set Ω)

  have hpow : ∀ k : ℕ, IsExp ε (fun τ => DD τ ^ k) (hD ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hC 1
      simpa [map_one] using this
    | succ k ih =>
      have e : (fun τ => DD τ ^ (k + 1)) = (fun τ => DD τ ^ k) * DD := by
        funext τ; simp [pow_succ]
      rw [e, pow_succ]
      exact (hops _ _ _ _ ih hDe).2.2
  have hprod : IsExp ε (fun τ => DD τ ^ w * f τ) (hD ^ w * h) := (hops _ _ _ _ (hpow w) hh).2.2
  have hEq : hD ^ w * h = H := huniq _ _ _ hprod hH
  have hDw0 : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hEq' : h = H * (hD⁻¹) ^ w := by
    rw [← hEq, inv_pow, mul_comm (hD ^ w) h, mul_assoc, mul_inv_cancel₀ hDw0, mul_one]

  have hHA : ∀ r, H.coeff r ∈ A := by
    intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hHa k]; exact hS k
    · push_neg at hr
      rw [hH0 r hr]; exact A.zero_mem
  have hDA : ∀ r, hD.coeff r ∈ A := by
    intro r
    obtain ⟨n, hn⟩ := hDz r
    rw [hn]; exact intCast_mem A n
  have hDiA : ∀ r, (hD⁻¹).coeff r ∈ A := hinv hD hDA (by rw [hDl, inv_one]; exact A.one_mem)
  have hpA : ∀ k : ℕ, ∀ r, ((hD⁻¹) ^ k).coeff r ∈ A := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [pow_zero]
      by_cases hr : r = 0
      · subst hr; simpa using A.one_mem
      · simpa [hr] using A.zero_mem
    | succ k ih =>
      intro r
      rw [pow_succ]
      exact hmul _ _ ih hDiA r
  refine ⟨S, fun r => ?_⟩
  rw [hEq']
  exact hmul _ _ hHA (hpA w) r

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_isExp : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f →
    ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  intro Ω _ ε f hf
  obtain ⟨N, w, hN, -, hq⟩ := hf
  obtain ⟨a, ha, hmem⟩ := hq 1
  choose b hb using fun n => (hmem n : a n ∈ ε.range)
  have hg : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    intro τ
    have := ha τ
    simp only [one_smul] at this
    simpa only [hb] using this
  obtain ⟨hg', hexg, -, -⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN hg
  obtain ⟨hD, hexD, hD0, -, -⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hring, -, hconst, -, hinv⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  have hDi := hinv DD hD hD0 hexD
  have hpow : ∀ k : ℕ, IsExp ε (DD⁻¹ ^ k) (hD⁻¹ ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hconst 1
      simp only [map_one, HahnSeries.C_one] at this
      rw [pow_zero, pow_zero]
      exact this
    | succ k ih =>
      simpa [pow_succ] using (hring _ _ _ _ ih hDi).2.2
  have hprod := (hring _ _ _ _ hexg (hpow w)).2.2
  refine ⟨hg' * hD⁻¹ ^ w, ?_⟩
  convert hprod using 1
  funext τ
  have := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  rw [inv_pow, mul_comm (DD τ ^ w), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ this), mul_one]

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sum_exp_fin_div (l : ℕ) (hl : 0 < l) (m : ℕ) :
    ∑ j : Fin l, cexp (2 * π * Complex.I * ((j : ℕ) * m : ℂ) / l) = if l ∣ m then (l : ℂ) else 0 := by
  have hl' : l ≠ 0 := hl.ne'
  set ζ : ℂ := cexp (2 * π * Complex.I / l)
  have hζ : IsPrimitiveRoot ζ l := Complex.isPrimitiveRoot_exp l hl'
  have e : ∀ j : ℕ, cexp (2 * π * Complex.I * ((j : ℂ) * m) / l) = (ζ ^ m) ^ j := by
    intro j
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) l]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem slz_repU (k l : ℕ) (hk : 1 ≤ k) (hl : 0 < l) (j : Fin l) (f : ℍ → ℂ) (τ : ℍ) :
    slz k (repU l j) f τ = (l : ℂ)⁻¹ * f (ofComplex (((τ : ℂ) + (j : ℕ)) / l)) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [slz, repU, Matrix.det_fin_two_of, pow_succ]
  field_simp
  simp

theorem polyB_Uo (l : ℕ) (a : ℕ → ℂ) (hl : 0 < l) (h : PolyB a) : PolyB (Uo l a) := by
  obtain ⟨C, A, hC⟩ := h
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    linarith [norm_nonneg (a 0)]
  refine ⟨C * (l : ℝ) ^ A, A, fun n => ?_⟩
  have h1 := hC (l * n)
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  calc ‖Uo l a n‖ = ‖a (l * n)‖ := rfl
    _ ≤ C * (((l * n : ℕ) : ℝ) + 1) ^ A := h1
    _ ≤ C * ((l : ℝ) * ((n : ℝ) + 1)) ^ A := by
        gcongr
        push_cast
        nlinarith
    _ = C * (l : ℝ) ^ A * ((n : ℝ) + 1) ^ A := by rw [mul_pow]; ring

theorem Uo_qs_sum_slz : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧
    ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  intro k l a hk hl ha
  refine ⟨polyB_Uo l a hl ha, fun τ => ?_⟩
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hpos : ∀ j : Fin l, 0 < (((τ : ℂ) + (j : ℕ)) / l).im := by
    intro j
    rw [Complex.div_natCast_im]
    exact div_pos (by simpa using τ.im_pos) (by exact_mod_cast hl)
  simp_rw [slz_repU k l hk hl _ (qs a) τ]
  have hqs : ∀ j : Fin l, qs a (ofComplex (((τ : ℂ) + (j : ℕ)) / l))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) := by
    intro j
    rw [ofComplex_apply_of_im_pos (hpos j)]
    rfl
  simp_rw [hqs]
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin l)),
      Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) :=
    fun j _ => ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 ⟨_, hpos j⟩).of_norm
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsum]
  have hinner : ∀ n : ℕ, ∑ j : Fin l, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l))
      = a n * cexp (2 * π * Complex.I * n * τ / l) * (if l ∣ n then (l : ℂ) else 0) := by
    intro n
    rw [← sum_exp_fin_div l hl n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hinner, ← tsum_mul_left]
  have hg : Function.Injective (fun m : ℕ => l * m) := fun x y h => Nat.eq_of_mul_eq_mul_left hl h
  rw [← hg.tsum_eq]
  · show ∑' m : ℕ, Uo l a m * cexp (2 * π * Complex.I * m * τ) = _
    refine tsum_congr fun m => ?_
    simp only [Uo, dvd_mul_right, if_true]
    rw [show (2 * π * Complex.I * ((l * m : ℕ) : ℂ) * τ / l : ℂ) = 2 * π * Complex.I * m * τ by
      push_cast
      field_simp]
    field_simp
  · intro n hn
    by_cases hd : l ∣ n
    · exact ⟨n / l, Nat.mul_div_cancel' hd⟩
    · exact (hn (by simp [hd])).elim

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.PetAdj

def toG (δ : M2) : GL (Fin 2) ℝ :=
  if hd : ((Int.castRingHom ℝ).mapMatrix δ).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

lemma toG_val (δ : M2) (hδ : δ.det ≠ 0) :
    (toG δ : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix δ := by
  have hd : ((Int.castRingHom ℝ).mapMatrix δ).det ≠ 0 := by
    rw [← RingHom.map_det]; simpa using hδ
  rw [toG, dite_eq_left hd]; rfl

lemma toG_det (δ : M2) (hδ : 0 < δ.det) : 0 < (toG δ).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toG_val δ hδ.ne', ← RingHom.map_det]
  simpa using hδ

def K (k N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (δ : M2) (τ : ℍ) : ℂ :=
  ch ε (δ 0 0) * (conj (h τ) * slz k δ f τ * (τ.im : ℂ) ^ k)

lemma ch_unit (N : ℕ) (ε : DirichletCharacter ℂ N) (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) :
    ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h0 : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγ
  have h2 : (((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ)) : ZMod N) = 1 := by rw [hdet]; simp
  push_cast at h2
  rw [h0, mul_zero, sub_zero] at h2
  simp only [ch, ← map_mul, h2, map_one]

lemma conj_ch_inv (N : ℕ) (ε : DirichletCharacter ℂ N) (x : ℤ) : conj (ch ε⁻¹ x) = ch ε x := by
  have := MulChar.star_apply' ε⁻¹ (x : ZMod N)
  simp only [inv_inv] at this
  exact this

lemma K_left (k L N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (hk : 1 ≤ k) (hNL : N ∣ L)
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (δ : M2) (hδ : 0 < δ.det)
    (hδN : (N : ℤ) ∣ δ 1 0) (τ : ℍ) :
    K k N ε h f ((γ : M2) * δ) τ = K k N ε h f δ τ := by
  obtain ⟨hcoc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k f hk
  have hγN : (N : ℤ) ∣ γ 1 0 := dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : slz k ((γ : M2) * δ) f τ = ch ε (γ 1 1) * slz k δ f τ := by
    rw [hcoc _ _ (by simp) hδ, (hinv L (ch ε)).mp hf γ hγ]
    simp only [slz]; ring
  have hd : ((δ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hδN
  have e : ch ε (((γ : M2) * δ) 0 0) = ch ε (γ 0 0) * ch ε (δ 0 0) := by
    simp only [ch, ← map_mul]
    congr 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  have hu := ch_unit N ε γ hγN
  simp only [K, h1, e]
  linear_combination (ch ε (δ 0 0) * (conj (h τ) * slz k δ f τ * (τ.im : ℂ) ^ k)) * hu

lemma K_right (k L N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (hk : 1 ≤ k) (hNL : N ∣ L)
    (hh : Inv k L (ch ε) h) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    K k N ε h f (δ * (γ : M2)) τ = K k N ε h f δ (γ • τ) := by
  have hcoc := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).1
  have hsl := (GlobalTheory.T.slashIntMatrixPosDet_properties k (slz k δ f) hk).2.1
  have hγN : (N : ℤ) ∣ γ 1 0 := dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have e2 := hh γ hγ τ
  have e1 := (congrFun (hcoc δ (γ : M2) hδ (by simp)) τ).trans (hsl γ τ)
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hj : ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have e3 := ModularGroup.im_smul_eq_div_normSq γ τ
  rw [hden] at e3
  generalize ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) = j at *
  have e3' : ((γ • τ).im : ℂ) = (τ.im : ℂ) / (j * conj j) := by
    rw [e3, Complex.mul_conj]; push_cast; rfl
  have hd : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγN
  have e4 : ch ε ((δ * (γ : M2)) 0 0) = ch ε (δ 0 0) * ch ε (γ 0 0) := by
    simp only [ch, ← map_mul]
    congr 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  have hu := ch_unit N ε γ hγN
  have hc : conj (ch ε (γ 1 1)) = ch ε (γ 0 0) := by
    have h1 : conj (ch ε (γ 1 1)) = (ch ε (γ 1 1))⁻¹ := by
      have := MulChar.star_apply' ε ((γ 1 1 : ℤ) : ZMod N)
      rw [MulChar.inv_apply_eq_inv'] at this
      exact this
    rw [h1]; exact (eq_inv_of_mul_eq_one_left hu).symm
  have hj' : conj j ≠ 0 := by simpa using hj
  simp only [K, e1, e2, e3', e4, map_mul, map_pow, hc, div_pow, mul_pow]
  field_simp

lemma K_adj (k N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (α : M2) (hα : 0 < α.det) (s : ℍ) :
    K k N ε h f α s = conj (ch ε⁻¹ (α 0 0) * slz k α.adjugate h (toG α • s)) * f (toG α • s) *
      ((toG α • s).im : ℂ) ^ k := by
  have hv := toG_val α hα.ne'
  have hden : denom (toG α) (s : ℂ) = ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) := by
    simp [denom, hv]
  have hnum : num (toG α) (s : ℂ) = ((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ) := by
    simp [num, hv]
  have hj : ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have ht := coe_smul_of_det_pos (toG_det α hα) s
  have him := im_smul_eq_div_normSq (toG α) s
  have hdet : (toG α).det.val = (α.det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hv, ← RingHom.map_det]; simp
  rw [abs_of_pos (toG_det α hα), hdet, hden] at him
  rw [hden, hnum] at ht
  generalize toG α • s = t at *
  have hQ : ((α.det : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hQe : ((α.det : ℤ) : ℂ) = (α 0 0 : ℂ) * (α 1 1 : ℂ) - (α 0 1 : ℂ) * (α 1 0 : ℂ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  have hda : α.adjugate.det = α.det := by
    rw [Matrix.det_adjugate]; simp
  have hA : ((α.adjugate 1 0 : ℤ) : ℂ) * t + ((α.adjugate 1 1 : ℤ) : ℂ)
      = ((α.det : ℤ) : ℂ) / (((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ)) := by
    rw [hQe, ht, Matrix.adjugate_fin_two, eq_div_iff hj]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (-((α 1 0 : ℤ) : ℂ) * (((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ))) * mul_inv_cancel₀ hj
  have hB : ((α.adjugate 0 0 : ℤ) : ℂ) * t + ((α.adjugate 0 1 : ℤ) : ℂ)
      = ((α.det : ℤ) : ℂ) * s / (((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ)) := by
    rw [hQe, ht, Matrix.adjugate_fin_two, eq_div_iff hj]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (((α 1 1 : ℤ) : ℂ) * (((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ))) * mul_inv_cancel₀ hj
  simp only [K, slz]
  rw [hA, hB, ← ht, hda, ofComplex_apply]
  generalize ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) = j at *
  have hs : ((α.det : ℤ) : ℂ) * s / j / (((α.det : ℤ) : ℂ) / j) = s := by field_simp
  have him' : (t.im : ℂ) = ((α.det : ℤ) : ℂ) * (s.im : ℂ) / (j * conj j) := by
    rw [him, Complex.mul_conj, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hj' : conj j ≠ 0 := by simpa using hj
  rw [hs, ofComplex_apply, him']
  simp only [map_mul, map_pow, map_inv₀, map_div₀, map_intCast, conj_ch_inv, div_pow, mul_pow]
  field_simp

end GlobalTheory.EisM.PetAdj


open GlobalTheory.EisM.PetAdj in
theorem GlobalTheory.EisM.pet_hsum_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (α : κ → M2) (h f : ℍ → ℂ), 1 ≤ k → 0 < N → N ∣ L → 0 < q → q.Coprime N → Wt L ρ → (∀ δ ∈ Δ, δ.det = q ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → RRep L Δ α → Inv k L (ch ε) h → Inv k L (ch ε) f → Continuous h → Continuous f → (∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (h τ) * slz k (β i) f τ * (τ.im : ℂ) ^ k))) → pet k ρ h (hsum k (ch ε) β f) = pet k ρ (fun τ => ∑ j, ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h τ) f := by
  intro k L N q ε ρ Δ ι κ _ _ β α h f hk _ hNL hq _ hρ hΔ hL hR hh hf hhc hfc hint
  have hcont := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).2.2.2.1
  have hβ : ∀ i, β i ∈ Δ := fun i => by
    simpa using hL.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
  have hα : ∀ j, α j ∈ Δ := fun j => by
    simpa using hR.mapsTo (Set.mem_univ (j, (1 : Gamma0 L)))
  have hdet : ∀ δ ∈ Δ, 0 < δ.det := fun δ hδ => by rw [(hΔ δ hδ).1]; exact_mod_cast hq
  have hΓ : ∀ γ : Gamma0 L, (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := fun γ =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  let eL : Gamma0 L × ι ≃ Δ := (Equiv.Set.univ _).symm.trans (Set.BijOn.equiv _ hL)
  let eR : κ × Gamma0 L ≃ Δ := (Equiv.Set.univ _).symm.trans (Set.BijOn.equiv _ hR)
  obtain ⟨e, he⟩ : ∃ e : Gamma0 L × ι ≃ κ × Gamma0 L, ∀ p : Gamma0 L × ι,
      ((p.1 : SL(2, ℤ)) : M2) * β p.2 = α (e p).1 * (((e p).2 : SL(2, ℤ)) : M2) :=
    ⟨eL.trans eR.symm, fun p => (congrArg Subtype.val (eR.apply_symm_apply (eL p))).symm⟩
  let φ : Gamma0 L →* GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ).comp (Gamma0 L).subtype
  have hφv : ∀ γ : Gamma0 L, (φ γ : Matrix (Fin 2) (Fin 2) ℝ)
      = (Int.castRingHom ℝ).mapMatrix ((γ : SL(2, ℤ)) : M2) := fun γ => rfl
  have hP : ∀ i, Integrable (fun x : ℍ => (ρ x : ℂ) * K k N ε h f (β i) x) := fun i => by
    refine ((hint i).const_mul (ch ε (β i 0 0))).congr (Eventually.of_forall fun x => ?_)
    simp only [K]; ring
  haveI : Countable SL(2, ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix; infer_instance
  obtain ⟨hQ, key⟩ := GlobalTheory.T.double_coset_adjoint_of_invariant_weight (GL (Fin 2) ℝ) ℍ (Gamma0 L) ι κ volume φ ρ (fun i => toG (β i))
    (fun j => toG (α j)) e (fun i => K k N ε h f (β i)) (fun j => K k N ε h f (α j))
    hρ.meas hρ.nonneg hρ.sum
    (fun p => by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hφv, hφv, toG_val _ (hdet _ (hβ _)).ne',
        toG_val _ (hdet _ (hα _)).ne', ← map_mul, ← map_mul, he])
    (fun p x => by
      rw [← K_left k L N ε h f hk hNL hf p.1 (hΓ _) _ (hdet _ (hβ _)) (hΔ _ (hβ _)).2, he,
        K_right k L N ε h f hk hNL hh _ (hΓ _) _ (hdet _ (hα _))]
      rfl)
    hP
    (fun j => by
      refine Continuous.aestronglyMeasurable ?_
      have := hcont _ (hdet _ (hα j)) hfc
      have him : Continuous fun τ : ℍ => (τ.im : ℂ) :=
        Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
      exact continuous_const.mul (((Complex.continuous_conj.comp hhc).mul this).mul (him.pow k)))
  have hC : ∀ j (x : ℍ), K k N ε h f (α j) ((toG (α j))⁻¹ • x) =
      conj (ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h x) * f x * (x.im : ℂ) ^ k := fun j x => by
    rw [K_adj k N ε h f _ (hdet _ (hα j)), smul_inv_smul]
  rw [← integral_finsetSum _ fun i _ => hP i, ← integral_finsetSum _ fun j _ => hQ j] at key
  simp only [hC] at key
  unfold pet hsum
  refine Eq.trans ?_ (key.trans ?_)
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [K, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)

    simp only [map_sum, Finset.mul_sum, Finset.sum_mul]

end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  first | exact @GlobalTheory.AlmostEt.QDer.exists_qDer | exact GlobalTheory.AlmostEt.QDer.exists_qDer | (intros; apply GlobalTheory.AlmostEt.QDer.exists_qDer <;> assumption)
end
