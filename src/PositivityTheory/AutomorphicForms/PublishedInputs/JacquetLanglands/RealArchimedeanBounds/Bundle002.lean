module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Bundle002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.AdelicNormalFormLemmas

theorem key {R : Type} [CommRing R] (c α r e r' e' : Rˣ) (u y0 : R) (k : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u * k) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0 * k)) := by
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0)) := by
    have hc := Units.inv_mul c
    have ha := Units.inv_mul α
    have hr := Units.mul_inv r'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply] <;>
      first
      | linear_combination (((α⁻¹ : Rˣ) : R) * α * r * e * r' * e') * hc + ((r : R) * e * r' * e') * ha
      | linear_combination ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hc - ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hr
      | linear_combination ((r : R) * e) * hc
  calc _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u)) * k := by group
    _ = _ := by rw [h1]; group

theorem jF_sa {F : Type} [Field F] [NumberField F] (c α : Fˣ) (β : F) :
    UpperTheory.Esk.jF F (Matrix.GeneralLinearGroup.scalar (Fin 2) c * aff α β) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ratU F c) * aff (ratU F α) (algebraMap F (Af F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.Esk.jF, ratU, aff, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]

end UpperTheory.Esk.AdelicNormalFormLemmas

open UpperTheory.Esk.AdelicNormalFormLemmas in
theorem UpperTheory.Esk.aBnf : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ACls → UpperTheory.Esk.AAdd → UpperTheory.Esk.ABnf := by
  intro hM hI hC hA F _ _
  classical
  obtain ⟨T, hT⟩ := hC F
  refine ⟨(T ×ˢ T).image (fun p => zc F p.1 * aff p.2 0), fun x => ?_⟩
  obtain ⟨d, a, u, k, hk, rfl⟩ := hI F x
  obtain ⟨y, e, r, hr, he, hd⟩ := hT d
  obtain ⟨y', e', r', hr', he', ha⟩ := hT a
  obtain ⟨y0, hy0⟩ := hA F r' ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u)
  have hK := (hM F).2.2.2.2.2.2.2
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) y⁻¹ * aff y'⁻¹ (-y0), ?_, zc F r * aff r' 0,
    Finset.mem_image.2 ⟨(r, r'), Finset.mem_product.2 ⟨hr, hr'⟩, rfl⟩,
    aff 1 (((r'⁻¹ : (Af F)ˣ) : Af F) * ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u - algebraMap F (Af F) y0)) *
      (zc F e * aff e' 0 * k), ?_, ?_⟩
  · simp [aff, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  · exact Subgroup.mul_mem _ ((hK 1 (by simp)).2 _ hy0)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK e he).1 ((hK e' he').2 0 (zero_mem _))) hk)
  · rw [jF_sa, map_inv, map_inv, map_neg, hd, ha]
    exact key (ratU F y) (ratU F y') r e r' e' u (algebraMap F (Af F) y0) k
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalingLemmas

def cb (K P1 P2 : ℝ) (n : ℕ) : ℝ := max (max 1 (K ^ n * P2)) (min 1 (P1 / K ^ n))⁻¹

theorem cb_pos (K P1 P2 : ℝ) (n : ℕ) : 0 < cb K P1 P2 n :=
  lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _))

theorem bal {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) {K P1 P2 : ℝ} (hK : 0 < K) (hP1 : 0 < P1)
    (ha : ∀ v, 0 < a v) (hb : ∀ v v', a v ≤ K * a v') (h1 : P1 ≤ ∏ v, a v) (h2 : ∏ v, a v ≤ P2) (v : ι) :
    (cb K P1 P2 (Fintype.card ι))⁻¹ ≤ a v ∧ a v ≤ cb K P1 P2 (Fintype.card ι) := by
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hKn : 0 < K ^ Fintype.card ι := pow_pos hK _
  have hup : a v ^ Fintype.card ι ≤ K ^ Fintype.card ι * P2 := by
    calc a v ^ Fintype.card ι = ∏ _v' : ι, a v := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ ∏ v' : ι, K * a v' := Finset.prod_le_prod₀ (fun _ _ => (ha v).le) fun v' _ => hb v v'
      _ = K ^ Fintype.card ι * ∏ v', a v' := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ K ^ Fintype.card ι * P2 := mul_le_mul_of_nonneg_left h2 hKn.le
  have hlo : P1 / K ^ Fintype.card ι ≤ a v ^ Fintype.card ι := by
    rw [div_le_iff₀ hKn]
    calc P1 ≤ ∏ v', a v' := h1
      _ ≤ ∏ _v' : ι, K * a v := Finset.prod_le_prod₀ (fun v' _ => (ha v').le) fun v' _ => hb v' v
      _ = a v ^ Fintype.card ι * K ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ, mul_comm]
  have hm : 0 < min 1 (P1 / K ^ Fintype.card ι) := lt_min one_pos (div_pos hP1 hKn)
  have hmv : min 1 (P1 / K ^ Fintype.card ι) ≤ a v := by
    rcases le_total (a v) 1 with h | h
    · exact le_trans (min_le_right _ _) (le_trans hlo (pow_le_of_le_one (ha v).le h hn))
    · exact le_trans (min_le_left _ _) h
  refine ⟨le_trans (inv_le_of_inv_le₀ hm (le_max_right _ _)) hmv, ?_⟩
  refine le_trans ?_ (le_max_left _ _)
  rcases le_total (a v) 1 with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans (le_self_pow₀ h hn) (le_trans hup (le_max_right _ _))

variable {F : Type} [Field F] [NumberField F]

def good (N : ℕ) (A : GF F) : Prop := ∀ i j, (N : Af F) * A.val i j ∈ Ohat F

theorem good_mul {a b : ℕ} {A B : GF F} (hA : good a A) (hB : good b B) : good (a * b) (A * B) := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_mul]
  have e : (a : Af F) * b * (A.val i 0 * B.val 0 j + A.val i 1 * B.val 1 j) =
      (a * A.val i 0) * (b * B.val 0 j) + (a * A.val i 1) * (b * B.val 1 j) := by ring
  rw [e]
  exact add_mem (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j))

theorem good_dvd {a b : ℕ} {A : GF F} (hA : good a A) (h : a ∣ b) : good b A := by
  obtain ⟨c, rfl⟩ := h
  intro i j
  rw [Nat.cast_mul, mul_comm (a : Af F), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hA i j)

omit [NumberField F] in
theorem scal_center (s : Fˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Subgroup.center (GL (Fin 2) F) :=
  Subgroup.mem_center_iff.2 fun g => Units.ext (Matrix.scalar_commute (n := Fin 2) (s : F) (fun _ => Commute.all _ _) g.val).symm.eq

theorem jF_scalar (s : Fˣ) : jF F (Matrix.GeneralLinearGroup.scalar (Fin 2) s) = zc F (ratU F s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jF, zc, ratU]

theorem det_jF (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F g) = ratU F (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [jF, ratU, Matrix.det_fin_two]

theorem zc_val (a : (Af F)ˣ) (i j : Fin 2) : (zc F a).val i j = if i = j then (a : Af F) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [zc]

theorem reAt_eq [IsTotallyReal F] (v : InfinitePlace F) (t : F) : reAt v t = sg v t := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

end UpperTheory.Esk.CentralScalingLemmas

namespace UpperTheory.Esk

open CentralScalingLemmas in
theorem dScale : AMem → ACls → AUnit → DScale := by
  intro hM hC hU F _ _ _ c hc χ ω
  obtain ⟨hK0, -, hKc, hHc, hdet, hint, hN, hunit⟩ := hM F
  obtain ⟨T, hT⟩ := hC F
  obtain ⟨C0, hC0, hU'⟩ := hU F
  obtain ⟨x, rfl⟩ : ∃ x : GF F, (x : GF F ⧸ Hc c) = ω := QuotientGroup.mk_surjective ω
  obtain ⟨N1, hN1, hx1⟩ := hN x
  obtain ⟨N2, hN2, hx2⟩ := hN x⁻¹
  choose Nf hNf0 hNf using hN
  have hzK : ∀ a : (Af F)ˣ, (a : Af F) ∈ Ohat F → ((a⁻¹ : (Af F)ˣ) : Af F) ∈ Ohat F → zc F a ∈ K0 F := by
    intro a h1 h2
    refine (hK0 _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [zc_val]; split_ifs
      · exact h1
      · exact zero_mem _
    · rw [← map_inv, zc_val]; split_ifs
      · exact h2
      · exact zero_mem _
  refine ⟨N1 * (∏ r ∈ T, Nf (zc F r)) * N2,
    cb (C0 ^ 2) (∑ r ∈ T, absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹
      (∑ r ∈ T, (absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹) (Fintype.card (InfinitePlace F)), ?_, cb_pos _ _ _ _, ?_⟩
  · exact Nat.mul_ne_zero (Nat.mul_ne_zero hN1 (Finset.prod_ne_zero_iff.2 fun r _ => hNf0 _)) hN2
  intro γ hγ
  induction γ using QuotientGroup.induction_on with
  | H γ₀ =>
  have h1 : x⁻¹ * (jF F γ₀ * x) ∈ Hc c := by
    have e : ((jF F γ₀ * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := hγ
    have := inv_mem (QuotientGroup.eq.1 e)
    convert this using 1
  obtain ⟨k, hk, z, hkz⟩ := (hHc c _).1 h1
  obtain ⟨y, u, r, hr, hu, hz⟩ := hT z
  set d : F := γ₀.val.det * ((y⁻¹ : Fˣ) : F) ^ 2 with hd
  have hd0 : d ≠ 0 := mul_ne_zero γ₀.det_ne_zero (pow_ne_zero _ (Units.ne_zero _))
  obtain ⟨ε, hε0, hεi, hεi', hεb⟩ := hU' (fun v => Real.sqrt (abs (sg v d)))
    (fun v => (Real.sqrt_pos.2 (abs_pos.2 ((map_ne_zero (sg v)).2 hd0))).ne')
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) F, g = γ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (y⁻¹ * Units.mk0 ε hε0) := ⟨_, rfl⟩
  have hK' : k * zc F (u * ratU F (Units.mk0 ε hε0)) ∈ K0 F := by
    refine mul_mem (hKc c hk) ?_
    rw [map_mul]
    refine mul_mem (hunit u hu).1 (hzK _ ?_ ?_)
    · exact (hint ε).1 hεi
    · rw [← map_inv]
      simpa [ratU] using (hint ε⁻¹).1 hεi'
  have hconj : x⁻¹ * (jF F g * x) = (k * zc F (u * ratU F (Units.mk0 ε hε0))) * zc F r := by
    have hjγ : jF F γ₀ = x * (k * zc F z) * x⁻¹ := by rw [← hkz]; group
    have hcomm := Subgroup.mem_center_iff.1 (zc_center (ratU F (y⁻¹ * Units.mk0 ε hε0))) x
    have hzS : z * ratU F (y⁻¹ * Units.mk0 ε hε0) = r * (u * ratU F (Units.mk0 ε hε0)) := by
      rw [hz, map_mul, map_inv]
      rw [show ratU F y * r * u * ((ratU F y)⁻¹ * ratU F (Units.mk0 ε hε0)) =
        (ratU F y * (ratU F y)⁻¹) * (r * (u * ratU F (Units.mk0 ε hε0))) by ac_rfl, mul_inv_cancel, one_mul]
    calc x⁻¹ * (jF F g * x)
        = x⁻¹ * (x * (k * zc F z) * x⁻¹ * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0)) * x) := by
          rw [hg, map_mul, jF_scalar, hjγ]
      _ = x⁻¹ * (x * (k * zc F z) * x⁻¹ * (x * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0)))) := by
          rw [mul_assoc _ (zc F _) x, ← hcomm]
      _ = k * (zc F z * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0))) := by group
      _ = k * zc F (r * (u * ratU F (Units.mk0 ε hε0))) := by rw [← map_mul, hzS]
      _ = k * zc F (u * ratU F (Units.mk0 ε hε0)) * zc F r := by rw [mul_comm r, map_mul, mul_assoc]
  have hjg : jF F g = x * ((k * zc F (u * ratU F (Units.mk0 ε hε0))) * zc F r) * x⁻¹ := by
    rw [← hconj]; group
  refine ⟨g, ?_, fun i j => ?_, ?_⟩
  · rw [hg, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (scal_center _), mul_one]
  ·
    have hgood : good (N1 * 1 * Nf (zc F r) * N2) (jF F g) := by
      rw [hjg, ← mul_assoc x]
      refine good_mul (good_mul (good_mul hx1 ?_) (hNf _)) hx2
      intro i j
      rw [Nat.cast_one, one_mul]
      exact ((hK0 _).1 hK').1 i j
    have hg2 := good_dvd (b := N1 * (∏ r ∈ T, Nf (zc F r)) * N2) hgood (by
      rw [mul_one]
      exact Nat.mul_dvd_mul (Nat.mul_dvd_mul_left _ (Finset.dvd_prod_of_mem _ hr)) dvd_rfl) i j
    refine (hint _).2 ?_
    rw [map_mul, map_natCast]
    exact hg2
  ·
    have hV : ∀ r' : (Af F)ˣ, 0 < absF (Matrix.GeneralLinearGroup.det (zc F r')) := fun r' => (Hm.absf F).1 _
    have habs : absF (ratU F (Matrix.GeneralLinearGroup.det g)) = absF (Matrix.GeneralLinearGroup.det (zc F r)) := by
      rw [← det_jF, hjg, map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det x), mul_assoc,
        mul_inv_cancel, mul_one, map_mul, (Hm.absf F).2.1, (Hm.absf F).2.2.1 _ fun w => (hdet _ hK' w).1, one_mul]
    have hprod : ∏ v, |sg v g.val.det| = (absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹ := by
      have := (Hm.absf F).2.2.2 (Matrix.GeneralLinearGroup.det g)
      have e : ∀ v, |reAt v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)| = |sg v g.val.det| := fun v => by
        rw [reAt_eq, Matrix.GeneralLinearGroup.val_det_apply]
      simp only [e] at this
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← habs]
      exact this
    have hdg : g.val.det = d * ε ^ 2 := by
      rw [hg, Units.val_mul, Matrix.det_mul, hd]
      simp [Matrix.det_fin_two]
      ring
    have ha : ∀ v, |sg v g.val.det| = |sg v ε * Real.sqrt (abs (sg v d))| ^ 2 := by
      intro v
      rw [hdg, map_mul, map_pow, abs_mul, sq_abs, mul_pow, Real.sq_sqrt (abs_nonneg _), abs_pow, sq_abs, mul_comm]
    intro v
    refine bal (fun v => |sg v g.val.det|) (pow_pos hC0 2) ?_ ?_ ?_ ?_ ?_ v
    · exact inv_pos.2 (lt_of_lt_of_le (hV r) (Finset.single_le_sum (fun r' _ => (hV r').le) hr))
    · intro v
      exact abs_pos.2 ((map_ne_zero (sg v)).2 g.det_ne_zero)
    · intro v v'
      rw [ha, ha, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hεb v v') 2
    · rw [hprod]
      exact inv_anti₀ (hV r) (Finset.single_le_sum (fun r' _ => (hV r').le) hr)
    · rw [hprod]
      exact Finset.single_le_sum (fun r' _ => (inv_pos.2 (hV r')).le) hr

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.GoodOperatorConjugation

variable {F : Type} [Field F] [NumberField F]

theorem v_lt_of_max {w : Pl F} {y : w.adicCompletionIntegers F}
    (hy : y ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F)) : Valued.v (y : w.adicCompletion F) < 1 := by
  refine lt_of_le_of_ne y.2 fun h1 => mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hy) ?_
  have h0 : (y : w.adicCompletion F) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have hi : (y : w.adicCompletion F)⁻¹ ∈ w.adicCompletionIntegers F := by
    show Valued.v ((y : w.adicCompletion F)⁻¹) ≤ 1
    rw [map_inv₀, h1, inv_one]
  exact ⟨⟨y, ⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

theorem congruence_subgroup_entry_valuations_alt {w : Pl F} {c : ℕ} (hc : c ≠ 0) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w c) :
    (∀ a b, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) a b) ≤ 1) ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) < 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) < 1 := by
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := Subgroup.mem_comap.1 hk
  change ![(0 : (w.adicCompletionIntegers F) ⧸ (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)), 1] ᵥ* _ =
    ![0, 1] at hk'
  rw [funext_iff, Fin.forall_fin_two] at hk'
  simp [Matrix.vecMul, dotProduct] at hk'
  obtain ⟨h1, h2⟩ := hk'
  have hle : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.pow_le_self hc
  refine ⟨fun a b => (k a b).2, v_lt_of_max (hle ?_), ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  · have : k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) :=
      hle (Ideal.Quotient.eq.1 (by rw [h2, map_one]))
    have h3 := v_lt_of_max this
    simpa using h3

theorem tr_conj {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.trace T := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem det_conj' {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.det (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.det T := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]

variable [IsTotallyReal F]

theorem good_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) : (mkDat c χ).Good a := by
  intro f hf x h
  have hf' : ∀ g (h : Hc c), f (g * h) = χ h * f g := hf
  have hzc : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  have hχz : ∀ z, χ ⟨zc F z, hzc z⟩ = ω.1 (finId F z) := fun z =>
    (hχ ⟨zc F z, hzc z⟩).2 1 (Subgroup.one_mem _) z (one_mul _).symm
  have hK : f ∈ Hi.fixd (Hi.rtr ℂ (GF F) ℂ) (Kc c) := by
    intro u hu
    funext g
    have hu' : u ∈ Hc c := Subgroup.mem_sup_left hu
    have h1 : χ ⟨u, hu'⟩ = 1 := by
      rw [(hχ ⟨u, hu'⟩).2 u hu 1 (by rw [map_one, mul_one]), map_one, map_one]
    rw [Hi.rtr_apply, hf' g ⟨u, hu'⟩, h1, Units.val_one, one_mul]
  have hs := (ha.act (GF F → ℂ) (Hi.rtr ℂ (GF F) ℂ) f hK).1
  obtain ⟨k, hk, z, hz⟩ := (hχ h).1
  have hfix := congrFun (hs k hk) x
  simp only [Hi.rtr_apply, Finset.sum_apply] at hfix
  change ∑ i, f (x * (h : GF F) * a i) = (χ h : ℂ) * ∑ i, f (x * a i)
  rw [(hχ h).2 k hk z hz, ← hχz z, ← hfix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hz, ← hf' (x * k * a i) ⟨zc F z, hzc z⟩]
  have hc := Subgroup.mem_center_iff.1 (zc_center z) (a i)
  congr 1
  simp only [mul_assoc]
  rw [hc]

theorem reg_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) {w : Pl F} (hw : w ∈ W) (hc : c w ≠ 0) : (mkDat c χ).Reg a := by
  classical
  intro γ x i hmem
  obtain ⟨k, hk, z, hz⟩ := (hχ ⟨_, hmem⟩).1
  have hz' : (a i)⁻¹ * (x⁻¹ * jF F γ * x) = k * zc F z := hz
  have e : x⁻¹ * jF F γ * x = a i * (k * zc F z) := by rw [← hz', mul_inv_cancel_left]
  obtain ⟨u, hu⟩ := ha.loc i w hc
  let φ : GF F →* GL (Fin 2) (w.adicCompletion F) := Matrix.GeneralLinearGroup.map (pLoc F w)
  let ψ : F →+* w.adicCompletion F := (pLoc F w).comp (algebraMap F (Af F))
  let r : ℕ := W.count w
  have hr : 0 < r := List.count_pos_iff.2 hw
  let p : w.adicCompletion F := ((atFin w (unif w) ^ r : (w.adicCompletion F)ˣ) : w.adicCompletion F)
  let zw : w.adicCompletion F := pLoc F w (z : Af F)
  have e2 := congrArg (fun g => ((φ g : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) e
  simp only [map_mul, map_inv, Units.val_mul] at e2
  obtain ⟨M, hMk⟩ : ∃ M : Matrix (Fin 2) (Fin 2) (w.adicCompletion F),
      ((φ k : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) = M := ⟨_, rfl⟩
  rw [hMk] at e2
  have hA : ((φ (a i) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![p, (u : w.adicCompletion F); 0, 1] := by
    rw [show φ (a i) = _ from hu]; rfl
  have hZ : ((φ (zc F z) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![zw, 0; 0, zw] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, zw, zc, Matrix.GeneralLinearGroup.map]
  have hT : ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![ψ (γ 0 0), ψ (γ 0 1); ψ (γ 1 0), ψ (γ 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have htr : ψ (γ.val.trace) = zw * (p * M 0 0 + u * M 1 0 + M 1 1) := by
    have := tr_conj (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of,
      Matrix.trace_fin_two_of] at this
    rw [Matrix.trace_fin_two, map_add (f := _)]
    change ψ (γ 0 0) + ψ (γ 1 1) = _
    rw [← this]; ring
  have hdet : ψ (γ.val.det) = zw ^ 2 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
    have := det_conj' (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.det_fin_two_of,
      Matrix.det_fin_two_of] at this
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
    change ψ (γ 0 0) * ψ (γ 1 1) - ψ (γ 0 1) * ψ (γ 1 0) = _
    rw [← this]; ring

  have hkl : φ k ∈ K1 w (c w) := Subgroup.mem_iInf.1 hk w
  obtain ⟨hM, hM10, hM11⟩ := congruence_subgroup_entry_valuations_alt hc hkl
  simp only [hMk] at hM hM10 hM11
  have hp : Valued.v p < 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    have h2 : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    show Valued.v (((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ^ r) < 1
    rw [map_pow, h1]
    exact pow_lt_one₀ zero_le h2 hr.ne'
  have hu1 : Valued.v (u : w.adicCompletion F) ≤ 1 := u.2
  have ht : Valued.v (p * M 0 0 + u * M 1 0 + M 1 1) = 1 := by
    have h1 : Valued.v (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) < 1 := by
      refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) hM11
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' (hM 0 0)) hp
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hu1) hM10
    rw [show p * M 0 0 + u * M 1 0 + M 1 1 = 1 + (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) by ring]
    exact Valuation.map_one_add_of_lt _ h1
  have hzw : zw ≠ 0 := (Units.map (pLoc F w).toMonoidHom z).ne_zero
  have ht0 : p * M 0 0 + u * M 1 0 + M 1 1 ≠ 0 := fun e => by rw [e, map_zero] at ht; exact zero_ne_one ht
  refine ⟨fun h0 => ?_, fun h4 => ?_⟩
  · rw [h0, map_zero] at htr
    exact mul_ne_zero hzw ht0 htr.symm
  · have h5 := congrArg ψ h4
    rw [map_pow, map_mul, htr, hdet, map_ofNat] at h5
    have h6 : (p * M 0 0 + u * M 1 0 + M 1 1) ^ 2 = 4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hzw)
      linear_combination h5
    have h7 := congrArg Valued.v h6
    rw [map_pow, ht, one_pow] at h7
    have h4v : Valued.v (4 : w.adicCompletion F) ≤ 1 := by
      have := natCast_mem (w.adicCompletionIntegers F) 4
      rw [Nat.cast_ofNat] at this
      exact this
    have hd : Valued.v (M 0 0 * M 1 1 - M 0 1 * M 1 0) ≤ 1 := by
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hM _ _) (hM _ _)
    have : Valued.v (4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0))) < 1 := by
      rw [map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h4v) (lt_of_le_of_lt (mul_le_of_le_one_right' hd) hp)
    exact absurd h7 (ne_of_gt this)

end UpperTheory.Esk.GoodOperatorConjugation

namespace UpperTheory.Esk

theorem dGood : AMem → DGood := by
  intro _ F _ _ _ c ω χ hχ W n a ha
  exact ⟨GoodOperatorConjugation.good_of hχ ha, fun ⟨w, hw, hc⟩ => GoodOperatorConjugation.reg_of hχ ha hw hc⟩

end UpperTheory.Esk
end
end
