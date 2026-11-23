module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle559
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle560
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.UnitFil

theorem isUnit_of_congr_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) → (∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l 1) → IsUnit B := by
  intro l _ K bk d k β B h1 h2
  obtain ⟨-, hker, hunit, haD, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    exact this
  have hl0 : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hB : ∀ i j, Per.θD l (B i j) = (1 : Matrix (Fin d) (Fin d) ℂ_[l]) i j := by
    intro i j
    have ha := (hker _).2 (h2 i j)
    obtain ⟨c, hc⟩ := h1 i j
    have hb : bk.ev (β i j) = (l : Ainf l) ^ k * bk.ev ((1 : Matrix (Fin d) (Fin d) bk.S) i j) + bk.ev bk.E * bk.ev c := by
      have : β i j = (l : bk.S) ^ k * (1 : Matrix (Fin d) (Fin d) bk.S) i j + bk.E * c := by
        rw [← hc]; simp [Matrix.sub_apply, Matrix.smul_apply]
      rw [this, map_add (f := _), map_mul, map_mul, map_pow, map_natCast]
    rw [map_sub, haD, hb, map_add (f := _), map_mul, map_mul, hE, zero_mul, add_zero, map_mul] at ha
    simp only [map_pow, map_natCast] at ha
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, mul_one] at ha ⊢
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i i) = (l : ℂ_[l]) ^ k * 1 := by
        rw [mul_one]; push_cast at ha; linear_combination -ha
      exact mul_left_cancel₀ hl0 ha'
    · simp only [Matrix.one_apply_ne hij, map_zero, mul_zero] at ha ⊢
      push_cast at ha
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i j) = 0 := by linear_combination -ha
      exact (mul_eq_zero.1 ha').resolve_left hl0
  have hmap : B.map (Per.θD l) = 1 := Matrix.ext hB
  rw [Matrix.isUnit_iff_isUnit_det]
  apply hunit
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]
  exact one_ne_zero

end GlobalTheory.BKLim.UnitFil
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

variable {l : ℕ} [Fact l.Prime]


variable (l) in
def ecoefQ (k₀ k i : ℕ) : ℚ_[l] := (l : ℚ_[l]) ^ k₀ * ((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹


variable (l) in
def ecoef (k₀ k i : ℕ) : ℤ_[l] :=
  ⟨if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0, by
    split_ifs with h
    · exact h
    · simp⟩

def kap (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) : Matrix (Fin d) (Fin d) (Per.Acris l) :=
  ∑ i ∈ Finset.range d, (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k i)) *
    (algebraMap (Ainf l) (Per.Acris l) (Per.zA l z) * C.t) ^ i) •
      (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ^ i

theorem ecoefQ_norm_le {d e m : ℕ} (k : ℕ) (hm : ¬ l ∣ m) (hd : d.factorial = l ^ e * m) {i : ℕ} (hi : i < d) :
    ‖ecoefQ l (e + k * d) k i‖ ≤ 1 := by
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hi.le
  obtain ⟨r, rfl⟩ : ∃ r, d = i + r := ⟨d - i, by omega⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hm0 : (m : ℚ_[l]) ≠ 0 := by
    rintro h
    exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  have h : (l : ℚ_[l]) ^ e * m = i.factorial * q := by
    exact_mod_cast (hd.symm.trans hq)
  have e1 : ecoefQ l (e + k * (i + r)) k i = (l : ℚ_[l]) ^ (k * r) * q * (m : ℚ_[l])⁻¹ := by
    unfold ecoefQ
    rw [show e + k * (i + r) = e + k * i + k * r by ring]
    field_simp
    rw [pow_add, pow_add]
    linear_combination ((l : ℚ_[l]) ^ (k * i) * (l : ℚ_[l]) ^ (k * r)) * h
  rw [e1, norm_mul, norm_mul, norm_inv, (Padic.norm_natCast_eq_one_iff (p := l)).2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hm), inv_one, mul_one]
  have h1 : ‖(l : ℚ_[l]) ^ (k * r)‖ ≤ 1 := by
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  have h2 : ‖(q : ℚ_[l])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (q : ℤ)
  calc ‖(l : ℚ_[l]) ^ (k * r)‖ * ‖(q : ℚ_[l])‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem ecoef_val {k₀ k i : ℕ} (h : ‖ecoefQ l k₀ k i‖ ≤ 1) :
    ((ecoef l k₀ k i : ℤ_[l]) : ℚ_[l]) = ecoefQ l k₀ k i := by
  show (if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0) = _
  rw [if_pos h]

theorem kap_zero (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) :
    kap C bk k₀ k Mn 0 = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold kap
  rw [Finset.sum_eq_single 0]
  · have h0 : ecoef l k₀ k 0 = (l : ℤ_[l]) ^ k₀ := by
      have hn : ‖ecoefQ l k₀ k 0‖ ≤ 1 := by
        simp only [ecoefQ, Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, inv_one]
        rw [norm_pow, Padic.norm_p]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
      apply Subtype.ext
      rw [ecoef_val hn]
      simp [ecoefQ]
    simp [h0]
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

end GlobalTheory.SstPer

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKFin

theorem finite_witt_quot (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [Finite F] [CharP F l] (n : ℕ) :
    Finite (WittVector l F ⧸ Ideal.span {(l : WittVector l F) ^ n}) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hker : RingHom.ker (WittVector.truncate (p := l) (R := F) n) =
      Ideal.span {(l : WittVector l F) ^ n} := by
    ext x
    rw [WittVector.mem_ker_truncate, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
  exact Finite.of_equiv _ ((Ideal.quotEquivOfEq hker).symm.trans
    (RingHom.quotientKerEquivOfSurjective (WittVector.truncate_surjective l n F))).toEquiv.symm

theorem finite_quot : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n c : ℕ),
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c})) := by
  intro l _ K bk n c
  haveI : Finite (Wq l bk.a ⧸ Ideal.span {(l : Wq l bk.a) ^ n}) := finite_witt_quot l (Fq l bk.a) n
  let J : Ideal (Wq l bk.a) := Ideal.span {(l : Wq l bk.a) ^ n}
  let I : Ideal bk.S := Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c}
  let g : (Fin c → Wq l bk.a ⧸ J) → bk.S ⧸ I := fun t => Ideal.Quotient.mk I
    (∑ i ∈ Finset.range c, C (if h : i < c then (t ⟨i, h⟩).out else 0) * X ^ i)
  refine Finite.of_surjective g ?_
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨fun i => Ideal.Quotient.mk J (coeff (i : ℕ) s), ?_⟩
  let w : ℕ → Wq l bk.a := fun i => if h : i < c then (Ideal.Quotient.mk J (coeff i s)).out else 0
  show Ideal.Quotient.mk I (∑ i ∈ Finset.range c, C (w i) * X ^ i) = Ideal.Quotient.mk I s
  rw [Ideal.Quotient.eq]
  have hw : ∀ i < c, w i - coeff i s ∈ J := by
    intro i hi
    simp only [w, dif_pos hi]
    rw [← Ideal.Quotient.eq]
    exact Ideal.Quotient.mk_out _
  have hsplit : (∑ i ∈ Finset.range c, C (w i) * X ^ i) - s =
      (∑ i ∈ Finset.range c, C (w i - coeff i s) * X ^ i) +
        ((∑ i ∈ Finset.range c, C (coeff i s) * X ^ i) - s) := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hw i (Finset.mem_range.1 hi))
    rw [← hy, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq', hm]

end GlobalTheory.BKFin
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_mul_sub_pow_dvd_of_dvd_sub : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  intro l _ K bk M m q hq
  obtain ⟨w, hw⟩ := bk.coeff_zero
  obtain ⟨t, ht⟩ := hq
  set P : bk.S := ((bk.Ep.divX : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) with hP
  have hE : bk.E = X * P + (l : bk.S) * C (w : Wq l bk.a) := by
    have h := Polynomial.X_mul_divX_add bk.Ep
    have h2 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) h
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, hw, map_mul,
      map_natCast] at h2
    change (bk.Ep : (Wq l bk.a)⟦X⟧) = _
    rw [← h2, hP]
    congr 2
    rw [← map_natCast (Polynomial.C (R := Wq l bk.a)), Polynomial.coe_C, map_natCast]
  have hu : C (w : Wq l bk.a) * C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a) = (1 : bk.S) := by
    rw [← map_mul, Units.mul_inv, map_one]
  set c' : bk.S := C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a)
  set a : bk.S := (l : bk.S) ^ (M + 1)
  set h₁ : bk.S := -((l : bk.S) ^ M + t * P) * c'
  set b : bk.S := bk.E * h₁
  have hqr : q * (-c' * P) = a + b := by
    simp only [a, b, h₁]
    linear_combination (-c' * P) * ht + (c' * (l : bk.S) ^ M) * hE + (l : bk.S) ^ (M + 1) * hu
  have key := geom_sum₂_mul a (-b) m
  rw [sub_neg_eq_add] at key
  refine ⟨(M + 1) * m, (-c' * P) * ∑ i ∈ Finset.range m, a ^ i * (-b) ^ (m - 1 - i), -((-h₁) ^ m), ?_⟩
  rw [pow_mul, ← mul_assoc, hqr, mul_comm (a + b), key]
  simp only [b]
  rw [neg_pow, mul_pow, neg_pow h₁]
  ring

end GlobalTheory.BSP.BK
end

section

attribute [local irreducible] Formalism.Per.σC Formalism.Per.σO Formalism.Per.φA Formalism.Per.zA Formalism.Per.AinfP Formalism.Per.zP Formalism.Per.toC Formalism.Per.θP Formalism.Per.kerP Formalism.Per.ev Formalism.Per.FilP Formalism.Per.θD Formalism.Per.pD Formalism.Per.zD Formalism.Per.FilD Formalism.Per.Acris0 Formalism.Per.Acris Formalism.Per.Bcris Formalism.Per.aB Formalism.Per.a0B Formalism.Per.zB Formalism.Per.φB Formalism.Per.σF Formalism.Per.σA Formalism.Per.extP Formalism.Per.σDp Formalism.Per.σD Formalism.Per.σB Formalism.Per.IsLog

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisFrobE

open scoped Nat

theorem pow_mul_factorial_dvd (l : ℕ) (hl : 0 < l) : ∀ n : ℕ, l ^ n * n ! ∣ (l * n)!
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_factorial_dvd l hl n
    have e : l * (n + 1) = (l * n + (l - 1)) + 1 := by rw [Nat.mul_succ]; omega
    have h2 : (l * n)! ∣ (l * n + (l - 1))! := Nat.factorial_dvd_factorial (by omega)
    have e2 : l ^ (n + 1) * (n + 1)! = (l * n + (l - 1) + 1) * (l ^ n * n !) := by
      rw [← e, Nat.factorial_succ, pow_succ]; ring
    rw [e2, e, Nat.factorial_succ]
    exact Nat.mul_dvd_mul_left _ (ih.trans h2)

theorem pow_succ_dvd_factorial (l : ℕ) (hl : 0 < l) : l ^ (l + 1) ∣ (l * l)! := by
  refine dvd_trans ?_ (pow_mul_factorial_dvd l hl l)
  rw [pow_succ]
  exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial hl le_rfl)

variable (l : ℕ) [Fact l.Prime]

theorem isUnit_natCast_ainfP (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Formalism.Per.AinfP l) :=
  GlobalTheory.AcrisDiscExt.isUnit_natCast_of (l := l) ((algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)).comp (Formalism.Per.zA l))
    (by
      have := IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l) (l : Formalism.Per.Ainf l)
      simpa using this) n hn

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE
open scoped Nat
variable (l : ℕ) [Fact l.Prime]

theorem coe_natCast0 (k : ℕ) : ((k : Formalism.Per.Acris0 l) : Formalism.Per.AinfP l) = k :=
  map_natCast (Formalism.Per.Acris0 l).val k

theorem exists_dpow (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) (n : ℕ) :
    ∃ d : Formalism.Per.Acris0 l, ((n ! : ℕ) : Formalism.Per.AinfP l) * (d : Formalism.Per.AinfP l) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := isUnit_natCast_ainfP l (n !) (Nat.factorial_ne_zero n)
  have key : ((n ! : ℕ) : Formalism.Per.AinfP l) *
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n * ((u⁻¹ : (Formalism.Per.AinfP l)ˣ) : Formalism.Per.AinfP l)) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
    rw [← hu, mul_comm, mul_assoc, Units.inv_mul, mul_one]
  exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n _ hx key⟩, key⟩

theorem exists_div_l (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) :
    ∃ y w : Formalism.Per.Acris0 l, (l : Formalism.Per.Acris0 l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) x ^ l ∧
      y ^ l = (l : Formalism.Per.Acris0 l) * w := by
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  set X := algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x with hX
  obtain ⟨g, hg⟩ := exists_dpow l x hx l
  obtain ⟨d, hd⟩ := exists_dpow l x hx (l * l)
  obtain ⟨m, hm⟩ := pow_succ_dvd_factorial l hl0
  have e : l * (l - 1)! = l ! := Nat.mul_factorial_pred hl0.ne'
  refine ⟨(((l - 1)! : ℕ) : Formalism.Per.Acris0 l) * g, (m : Formalism.Per.Acris0 l) * d, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, coe_natCast0,
      coe_natCast0, ← hX, ← hg, ← mul_assoc, ← Nat.cast_mul, e]
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, coe_natCast0,
      coe_natCast0, coe_natCast0]
    refine ((isUnit_natCast_ainfP l (l ^ l) (pow_ne_zero _ hl0.ne')).mul_right_inj).1 ?_
    have h1 : ((l ^ l : ℕ) : Formalism.Per.AinfP l) * ((((l - 1)! : ℕ) : Formalism.Per.AinfP l) * (g : Formalism.Per.AinfP l)) ^ l =
        X ^ (l * l) := by
      rw [pow_mul, ← hg, ← e, Nat.cast_mul, Nat.cast_pow, ← mul_pow]; ring
    rw [h1, ← hd, hm]
    push_cast; ring

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∃ v : (Per.Acris l)ˣ, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) = (l : Per.Acris l) * v) ∧ (∀ a : Ainf l, phiA l ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) ∧ ∀ (g : GQ l) (a : Ainf l), sigA g ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (Per.σA g a) := by
  intro l _ K bk
  obtain ⟨htor, hcomp, -, -⟩ := GlobalTheory.Per.acris_basic l
  haveI := hcomp
  refine ⟨htor, hcomp, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := bk.isUnit_δ
    have hφ : frobS l bk.a bk.E = bk.E ^ l + (l : bk.S) * (u : bk.S) := by
      rw [hu]; exact (deltaS l bk.a).φ_eq bk.E
    have hx : Formalism.Per.θ l (bk.ev bk.E) = 0 := by
      have h : bk.ev bk.E ∈ RingHom.ker (Formalism.Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact h
    obtain ⟨y, w, hy, hw⟩ := exists_div_l l _ hx
    set j := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) with hj
    set a := algebraMap (Ainf l) (Formalism.Per.Acris l) with ha_def
    have ha : ∀ t, a t = j (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) t) :=
      fun t => GlobalTheory.RingIface.tower l t
    set A : Formalism.Per.Acris l := a (bk.ev (u : bk.S)) with hA
    have hAu : IsUnit A := (u.isUnit.map bk.ev).map a
    obtain ⟨U, hU⟩ := hAu
    set Y := j y with hY
    set z := ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) * Y with hz_def
    have hz : z ^ l ∈ Ideal.span {(l : Formalism.Per.Acris l)} := by
      rw [hz_def, mul_pow, show Y ^ l = (l : Formalism.Per.Acris l) * j w by rw [hY, ← map_pow, hw, map_mul, map_natCast]]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    have hJ : (-z) ^ l ∈ (⊥ : Ideal (Formalism.Per.Acris l)).jacobson := by
      refine IsAdicComplete.le_jacobson_bot (Ideal.span {(l : Formalism.Per.Acris l)}) ?_
      rw [neg_pow]; exact Ideal.mul_mem_left _ _ hz
    have h1 : IsUnit (1 - (-z) ^ l) := by
      have := Ideal.mem_jacobson_bot.1 hJ (-1)
      rwa [mul_neg_one, neg_add_eq_sub] at this
    have h2 : IsUnit (1 + z) := by
      rw [← mul_neg_geom_sum, sub_neg_eq_add] at h1
      exact isUnit_of_mul_isUnit_left h1
    obtain ⟨V, hV⟩ := h2
    refine ⟨U * V, ?_⟩
    have hUU : (U : Formalism.Per.Acris l) * ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) = 1 := U.mul_inv
    have hxl : a (bk.ev bk.E) ^ l = (l : Formalism.Per.Acris l) * Y := by
      rw [ha, ← map_pow, ← hy, map_mul, map_natCast]
    rw [RingHom.comp_apply, hφ, map_add (f := _), map_mul, map_pow, map_natCast, map_add (f := _), map_pow, map_mul, map_natCast, hxl,
      Units.val_mul, hV, hU, hz_def]
    rw [← hA]
    rw [hU] at hUU
    linear_combination (-(l : Formalism.Per.Acris l) * Y) * hUU
  · intro a
    rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    ext n
    rw [GlobalTheory.RingIface.phiA_coeff l a n, WittVector.coeff_frobenius_charP]
  · intro g a
    rw [(GlobalTheory.CrisMaps.sigA_extends g).alg]

end GlobalTheory.AcrisFrobE
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.ThetaPer

theorem thetaD_aDp_pow_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (n : ℕ), ((Per.θD l).comp (aDp l)) (τ ^ n) ≠ 0 := by
  intro l _ K bk τ hτ n
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hinj : Function.Injective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro x y h
    rw [WittVector.frobenius_eq_map_frobenius] at h
    exact WittVector.map_injective _ (frobeniusEquiv (OCb l) l).injective h
  have hpi : WittVector.frobenius (GlobalTheory.MemLoc.TiedUnif.piOne ε) = WittVector.teichmuller l ε - 1 := by
    rw [GlobalTheory.MemLoc.TiedUnif.piOne, map_sub, map_one, WittVector.frobenius_eq_map_frobenius]
    change WittVector.map (frobenius (OCb l) l) (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm ε)) - 1 = _
    rw [WittVector.map_teichmuller, frobenius_apply_frobeniusEquiv_symm]
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro y
    obtain ⟨x, hx⟩ := WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective y
    exact ⟨x, by rw [WittVector.frobenius_eq_map_frobenius]; exact hx⟩
  obtain ⟨η₀, hη₀⟩ := hsurj (η : Ainf l)
  obtain ⟨η₁, hη₁⟩ := hsurj ((η⁻¹ : (Ainf l)ˣ) : Ainf l)
  have hu : η₀ * η₁ = 1 := hinj (by rw [map_mul, map_one, hη₀, hη₁, Units.mul_inv])
  have hτe : τ = η₀ * GlobalTheory.MemLoc.TiedUnif.piOne ε := hinj (by rw [hφ, map_mul, hη₀, hpi])
  set f := (Per.θD l).comp (aDp l)
  have hf0 : f η₀ ≠ 0 := by
    intro h
    have := congrArg f hu
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hf1 : f (GlobalTheory.MemLoc.TiedUnif.piOne ε) ≠ 0 := GlobalTheory.MemLoc.TiedUnif.theta_piOne hε
  rw [map_pow, hτe, map_mul]
  exact pow_ne_zero _ (mul_ne_zero hf0 hf1)

end GlobalTheory.ThetaPer
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s, ‖toDisc l (s X) ρ x‖ ≤ r := by
  first | exact @GlobalTheory.BSP.norm_toDisc_J_pow_small | exact GlobalTheory.BSP.norm_toDisc_J_pow_small | (intros; apply GlobalTheory.BSP.norm_toDisc_J_pow_small <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ ((l : ℝ)⁻¹ ≤ bk.ρ₀) ∧ ‖toDisc l (s X) bk.ρ₀ (s bk.E)‖ ≤ (l : ℝ)⁻¹ := by
  first | exact @GlobalTheory.BSP.norm_E_le_radius | exact GlobalTheory.BSP.norm_E_le_radius | (intros; apply GlobalTheory.BSP.norm_E_le_radius <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧ ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  first | exact @GlobalTheory.BSP.isUnit_inclW_per_and_saturated | exact GlobalTheory.BSP.isUnit_inclW_per_and_saturated | (intros; apply GlobalTheory.BSP.isUnit_inclW_per_and_saturated <;> assumption)
end
