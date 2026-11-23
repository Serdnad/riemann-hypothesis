module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.CmpP

variable {F : Type} [Field F] [NumberField F]

theorem pint_mul {p : ℕ} {x y : F} (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) := fun w hw => by
  rw [map_mul]; exact mul_le_one' (hx w hw) (hy w hw)

theorem pint_add {p : ℕ} {x y : F} (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) := fun w hw =>
  Valuation.map_add_le _ (hx w hw) (hy w hw)

theorem punit_mul {p : ℕ} {x y : F} (hx : PUnit p x) (hy : PUnit p y) : PUnit p (x * y) := fun w hw => by
  rw [map_mul, hx w hw, hy w hw, mul_one]

theorem reAt_eq [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_re]

theorem tp_mul [IsTotallyReal F] {x y : F} (hx : TP x) (hy : TP y) : TP (x * y) := fun v => by
  have := mul_pos (hx v) (hy v); rw [reAt_eq] at this ⊢; rw [reAt_eq] at this; simpa [map_mul] using this

theorem tp_one [IsTotallyReal F] : TP (1 : F) := fun v => by rw [reAt_eq, map_one]; exact one_pos

theorem abs_norm_eq [IsTotallyReal F] (x : F) : |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ v, |reAt v x| := by
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : v.IsReal := IsTotallyReal.isReal v
  have hm : v.mult = 1 := by simp [InfinitePlace.mult, hv]
  rw [hm, pow_one, reAt, ← InfinitePlace.norm_embedding_eq, ← InfinitePlace.embedding_of_isReal_apply hv,
    Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]

end GlobalTheory.HilbertThetaSeries.CmpP

namespace GlobalTheory.HilbertThetaSeries.CmpP

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem inG_mul {p : ℕ} {δ : F} (hδ0 : δ ≠ 0) {γ γ' : GL (Fin 2) F} (h : InG p δ γ) (h' : InG p δ γ') :
    InG p δ (γ * γ') := by
  obtain ⟨a, b, c, d, de, dt⟩ := h
  obtain ⟨a', b', c', d', de', dt'⟩ := h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (γ * γ').val 0 0 = γ.val 0 0 * γ'.val 0 0 + (δ * γ.val 0 1) * (γ'.val 1 0 / δ) := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
    rw [this]; exact pint_add (pint_mul a a') (pint_mul b c')
  · have : δ * (γ * γ').val 0 1 = γ.val 0 0 * (δ * γ'.val 0 1) + (δ * γ.val 0 1) * γ'.val 1 1 := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [this]; exact pint_add (pint_mul a b') (pint_mul b d')
  · have : (γ * γ').val 1 0 / δ = (γ.val 1 0 / δ) * γ'.val 0 0 + γ.val 1 1 * (γ'.val 1 0 / δ) := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [this]; exact pint_add (pint_mul c a') (pint_mul d c')
  · have : (γ * γ').val 1 1 = (γ.val 1 0 / δ) * (δ * γ'.val 0 1) + γ.val 1 1 * γ'.val 1 1 := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
    rw [this]; exact pint_add (pint_mul c b') (pint_mul d d')
  · rw [Units.val_mul, Matrix.det_mul]; exact punit_mul de de'
  · rw [Units.val_mul, Matrix.det_mul]; exact tp_mul dt dt'

theorem inG_one (p : ℕ) (δ : F) : InG p δ 1 := by
  have h1 : PInt p (1 : F) := fun w _ => by rw [map_one]
  have h0 : PInt p (0 : F) := fun w _ => by rw [map_zero]; exact zero_le'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h1, h0]
  · intro w _; simp
  · exact tp_one

end GlobalTheory.HilbertThetaSeries.CmpP

namespace GlobalTheory.HilbertThetaSeries.CmpP

section Alg
variable {M : Type} [CommGroupWithZero M] {a z t d c s : M}

theorem alg1 (ha : a * z = 1) (ht : t ≠ 0) (h : c * t = z * t * s) : a * c = s :=
  mul_right_cancel₀ ht (by rw [mul_assoc, h, ← mul_assoc, ← mul_assoc, ha, one_mul, mul_comm])

theorem alg2 (ha : a * z = 1) (hd : t * d = 1) (h : c = z * t * s) : d * (a * c) = s := by
  rw [h]; calc d * (a * (z * t * s)) = (a * z) * (t * d) * s := by ac_rfl
    _ = s := by rw [ha, hd, one_mul, one_mul]

theorem alg3 (ha : a * z = 1) (hd : t * d = 1) (h : c * t = z * s) : a * c / d = s := by
  have hd0 : d ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have : d⁻¹ = t := (eq_inv_of_mul_eq_one_left hd).symm
  rw [div_eq_mul_inv, this, mul_assoc, h, ← mul_assoc, ha, one_mul]

theorem alg4 (ha : a * z = 1) (h : c = z * s) : a * c = s := by rw [h, ← mul_assoc, ha, one_mul]

theorem alg5 (ha : a * z = 1) (ht : t ≠ 0) (h : c * t = z ^ 2 * t * s) : a ^ 2 * c = s :=
  mul_right_cancel₀ ht (by
    calc a ^ 2 * c * t = a ^ 2 * (c * t) := by rw [mul_assoc]
      _ = (a * z) ^ 2 * s * t := by rw [h, mul_pow]; ac_rfl
      _ = s * t := by rw [ha, one_pow, one_mul])
end Alg

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rep_cmp {p : ℕ} [hp : Fact p.Prime] {δ : F} (hδ : IsDel p δ) (y y' z : (Af F)ˣ) (γ : GL (Fin 2) F)
    (u : GL (Fin 2) (Af F)) (hy : AtP p δ y) (hy' : AtP p δ y') (hT : TP γ.val.det) (hu : u ∈ KLev F 2 1)
    (heq : toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u) :
    ∃ (η : Fˣ) (r : ℚ), InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) ∧ 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧
      |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det : ℚ) : ℝ)| * absF y' =
        (r : ℝ) ^ 2 * absF y := by
  obtain ⟨ξ, hξT, hξ⟩ := (GlobalTheory.HilbertThetaSeries.del_exists_and_move F p hp.out).2 δ hδ (z * y)
  have hK := ((GlobalTheory.HilbertThetaSeries.kMem F).1 u).1 hu
  have hV := (GlobalTheory.HilbertThetaSeries.kMem F).2.2.2.1
  have e := congrArg (fun g : GL (Fin 2) (Af F) => g.val) heq
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp [toFin, aff, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have edet : algebraMap F (Af F) γ.val.det * y = z ^ 2 * y' * u.val.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]
    linear_combination (algebraMap F (Af F) (γ.val 1 1)) * e00 + ((z : Af F) * y' * u.val 0 0) * e11 -
      (algebraMap F (Af F) (γ.val 0 1)) * e10 - ((z : Af F) * u.val 1 0) * e01
  have hs : ∀ i j, (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ).val i j = (ξ : F) * γ.val i j := by
    intro i j; fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  have hsd : (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ).val.det = (ξ : F) ^ 2 * γ.val.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, hs, hs, hs, hs]; ring
  have key : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
      Valued.v (pLoc F w (algebraMap F (Af F) ξ)) * Valued.v (pLoc F w (z : Af F)) = 1 ∧
      Valued.v (pLoc F w (y' : Af F)) = Valued.v (pLoc F w (y : Af F)) ∧
      Valued.v (pLoc F w (y : Af F)) * w.valuation F δ = 1 := by
    intro w hw
    have h1 := hy w hw
    have h2 := hy' w hw
    have h3 := hξ w hw
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul] at h3
    have hd0 : w.valuation F δ ≠ 0 := right_ne_zero_of_mul_eq_one h1
    refine ⟨?_, mul_right_cancel₀ hd0 (h2.trans h1.symm), h1⟩
    calc _ = Valued.v (pLoc F w (algebraMap F (Af F) ξ)) * Valued.v (pLoc F w (z : Af F)) *
          (Valued.v (pLoc F w (y : Af F)) * w.valuation F δ) := by rw [h1, mul_one]
      _ = 1 := by rw [← h3]; ac_rfl
  have push : ∀ (w : HeightOneSpectrum (𝓞 F)) {a b : Af F}, a = b → Valued.v (pLoc F w a) = Valued.v (pLoc F w b) :=
    fun w _ _ h => by rw [h]
  have hG : InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ) := by
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e00
      simp only [map_mul, k2] at h
      rw [hs, map_mul, ← hV, ← hV, alg1 k1 (left_ne_zero_of_mul_eq_one k3) h]
      exact hK.1 w 0 0
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e01
      simp only [map_mul, k2] at h
      rw [hs, map_mul, map_mul, ← hV ξ, ← hV (γ.val 0 1), alg2 k1 k3 h]
      exact hK.1 w 0 1
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e10
      simp only [map_mul] at h
      rw [hs, map_div₀, map_mul, ← hV ξ, ← hV (γ.val 1 0), alg3 k1 k3 h]
      exact hK.1 w 1 0
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e11
      simp only [map_mul] at h
      rw [hs, map_mul, ← hV, ← hV, alg4 k1 h]
      exact hK.1 w 1 1
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w edet
      simp only [map_mul, map_pow, k2] at h
      rw [hsd, map_mul, map_pow, ← hV, ← hV, alg5 k1 (left_ne_zero_of_mul_eq_one k3) h]
      exact hK.2 w
    · rw [hsd, sq]; exact tp_mul (tp_mul hξT hξT) hT
  obtain ⟨-, hmul, hone, hprod⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨r, hr, hr1, hrz⟩ := GlobalTheory.HilbertThetaSeries.IdeleAbs.absF_eq_rat F p (Units.map (algebraMap F (Af F)).toMonoidHom ξ * z) fun w hw => by
    simpa only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul] using (key w hw).1
  have hid : Units.map (algebraMap F (Af F)).toMonoidHom
        (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ)) * y =
      (Units.map (algebraMap F (Af F)).toMonoidHom ξ * z) * (Units.map (algebraMap F (Af F)).toMonoidHom ξ * z) * y' *
        Matrix.GeneralLinearGroup.det u := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    rw [← Units.val_mul, hsd, map_mul, map_pow]
    linear_combination (algebraMap F (Af F) ξ) ^ 2 * edet
  have h1 := hprod (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ))
  have h2 := congrArg absF hid
  rw [hmul, hmul, hmul, hmul, hrz, hone (Matrix.GeneralLinearGroup.det u) hK.2, mul_one] at h2
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← abs_norm_eq] at h1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨ξ, r⁻¹, hG, inv_pos.2 hr, by rw [Rat.cast_inv, norm_inv, hr1, inv_one], ?_⟩
  rw [Rat.cast_inv, inv_pow, eq_inv_mul_iff_mul_eq₀ (pow_pos hr' 2).ne']
  linear_combination absF y * h1 -
    |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ).val.det : ℚ) : ℝ)| * h2

end GlobalTheory.HilbertThetaSeries.CmpP

theorem GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (δ : F), IsDel p δ → (∀ γ γ' : GL (Fin 2) F, InG p δ γ → InG p δ γ' → InG p δ (γ * γ')) ∧ InG p δ 1 ∧ ∀ (y y' z : (Af F)ˣ) (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), AtP p δ y → AtP p δ y' → TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → ∃ (η : Fˣ) (r : ℚ), InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) ∧ 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det : ℚ) : ℝ)| * absF y' = (r : ℝ) ^ 2 * absF y :=
  fun F _ _ _ p hp δ hδ =>
    ⟨fun _ _ h h' => GlobalTheory.HilbertThetaSeries.CmpP.inG_mul (GlobalTheory.HilbertThetaSeries.denominators_prime_to F p hp.out δ hδ).1 h h', GlobalTheory.HilbertThetaSeries.CmpP.inG_one p δ,
      fun y y' z γ u hy hy' hT hu heq => GlobalTheory.HilbertThetaSeries.CmpP.rep_cmp hδ y y' z γ u hy hy' hT hu heq⟩

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_inG_scalar_mul_and_abs_norm_det_mul_absF_eq : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (δ : F), IsDel p δ → (∀ γ γ' : GL (Fin 2) F, InG p δ γ → InG p δ γ' → InG p δ (γ * γ')) ∧ InG p δ 1 ∧ ∀ (y y' z : (Af F)ˣ) (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), AtP p δ y → AtP p δ y' → TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → ∃ (η : Fˣ) (r : ℚ), InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) ∧ 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det : ℚ) : ℝ)| * absF y' = (r : ℝ) ^ 2 * absF y := by
  first | exact @GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p | exact GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p | (intros; apply GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem sum_isReps_add_shift {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (T : Finset V)
    (hT : IsReps A B T) (f : V → ℂ) (hf : ∀ x ∈ B, ∀ m ∈ A, f (x + m) = f x) (s : V) (hs : s ∈ B) :
    ∑ x ∈ T, f (x + s) = ∑ x ∈ T, f x := by
  classical
  obtain ⟨hTB, huniq⟩ := hT
  have key : ∀ x ∈ B, ∃ y ∈ T, x - y ∈ A := fun x hx => by
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := huniq x hx
    exact ⟨y, hy, hxy⟩
  choose! g hgT hgA using key
  have hfx : ∀ x ∈ T, f (x + s) = f (g (x + s)) := by
    intro x hx
    have hxs : x + s ∈ B := B.add_mem (hTB x hx) hs
    have h := hf (g (x + s)) (hTB _ (hgT _ hxs)) _ (hgA _ hxs)
    rw [← h]
    congr 1
    abel
  rw [Finset.sum_congr rfl hfx]
  apply Finset.sum_nbij (fun x => g (x + s))
  · intro x hx
    exact hgT _ (B.add_mem (hTB x hx) hs)
  · intro x hx x' hx' h
    simp only [Finset.mem_coe] at hx hx'
    have h1 := hgA _ (B.add_mem (hTB x hx) hs)
    have h2 := hgA _ (B.add_mem (hTB x' hx') hs)
    simp only at h
    rw [h] at h1
    have hd : x - x' ∈ A := by
      have h3 := A.sub_mem h1 h2
      convert h3 using 1
      abel
    obtain ⟨y, _, hy⟩ := huniq x (hTB x hx)
    have e1 := hy x ⟨hx, by rw [sub_self]; exact A.zero_mem⟩
    have e2 := hy x' ⟨hx', hd⟩
    rw [e1, e2]
  · intro y hy
    simp only [Finset.mem_coe] at hy
    have hys : y - s ∈ B := B.sub_mem (hTB y hy) hs
    refine ⟨g (y - s), hgT _ hys, ?_⟩
    have hxs : g (y - s) + s ∈ B := B.add_mem (hTB _ (hgT _ hys)) hs
    apply (huniq _ hxs).unique ⟨hgT _ hxs, hgA _ hxs⟩ ⟨hy, ?_⟩
    have h4 := A.neg_mem (hgA _ hys)
    convert h4 using 1
    abel
  · intro x hx
    rfl

theorem gaussSum_dual_shift : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  intro F _ _ κ _ _ G hG N a b c d T hN hNy ha hb hcN hd hdet hc hT y hy
  obtain ⟨hBsymm, hsmul, hBadd, hint, hLLiff, haL, het, hLLdual⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  obtain ⟨-, -, hdd, -, -⟩ := GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
  have etadd : ∀ u v : F, et (u + v) = et u * et v := fun u v => (het u v).1
  have etint : ∀ u : F, IsIntegral ℤ u → et u = 1 := fun u hu => (het u 0).2.2.2 hu
  have etiff : ∀ u : F, et u = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F u = n := fun u => (het u 0).2.2.1
  have hLLsmul : ∀ r : F, IsIntegral ℤ r → ∀ x ∈ LL F κ, r • x ∈ LL F κ := by
    intro r hr x hx
    rw [hLLiff] at hx ⊢
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using hr.mul (hx i)
  have hB1 : ∀ x, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := by
    intro x
    rw [haL]
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa using hl
    · intro hx
      exact ⟨x, hx, by simp⟩
  have hdualet : ∀ w ∈ dualL F G, ∀ l ∈ LL F κ, et (BF G w l) = 1 := by
    intro w hw l hl
    exact (etiff _).2 (hw l hl)
  have hexp : ∀ (x : κ → F) (r : F) (z : κ → F),
      QF G (x + r • z) = QF G x + r * BF G x z + r ^ 2 * QF G z := by
    intro x r z
    rw [(hBsymm x (r • z)).2, (hBsymm x (r • z)).1, (hsmul r z x).1, (hsmul r z x).2.1,
      (hBsymm z x).1]
  have hBlin : ∀ (y x : κ → F) (r : F) (z : κ → F),
      BF G y (x + r • z) = BF G y x + r * BF G y z := by
    intro y x r z
    rw [(hBsymm y (x + r • z)).1, hBadd, (hsmul r z y).1, (hBsymm x y).1, (hBsymm z y).1]
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcw : ∀ w ∈ dualL F G, c • w ∈ LL F κ := by
    intro w hw
    have e : c • w = (c / N) • ((N : F) • w) := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [e]
    exact hLLsmul _ hcN _ (hNy w hw).1
  have hcQ : ∀ w ∈ dualL F G, IsIntegral ℤ (a * c * QF G w) := by
    intro w hw
    have e : a * c * QF G w = a * (c / N) * ((N : F) * QF G w) := by
      field_simp
    rw [e]
    exact (ha.mul hcN).mul (hNy w hw).2
  have haB : ∀ x ∈ LL F κ, ∀ w ∈ dualL F G, et (a * BF G x w) = 1 := by
    intro x hx w hw
    rw [← (hsmul a x w).1, (hBsymm _ w).1]
    exact hdualet w hw _ (hLLsmul a ha x hx)
  have hg : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
      et (a / c * QF G (x + m)) = et (a / c * QF G x) := by
    intro x hx m hm
    rw [hB1] at hx
    obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
    rw [hexp]
    have e : a / c * (QF G x + c * BF G x l + c ^ 2 * QF G l)
        = a / c * QF G x + (a * BF G x l + a * c * QF G l) := by
      field_simp
      ring
    rw [e, etadd, etint _ ((ha.mul ((hint x hx).2 l hl)).add (hcQ l (hLLdual hl))), mul_one]
  by_cases hyL : y ∈ LL F κ
  · have h1 : oneL y = 1 := by simp [oneL, hyL]
    rw [h1, one_mul, Finset.sum_mul]
    have hs : d • y ∈ aL κ (1 : F) := (hB1 _).2 (hLLsmul d hd y hyL)
    refine Eq.trans ?_ (sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x)) hg (d • y) hs)
    apply Finset.sum_congr rfl
    intro x hxT
    have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
    rw [hexp]
    have key : a / c * (QF G x + d * BF G x y + d ^ 2 * QF G y)
        = a / c * QF G x + BF G y x / c + d / c * QF G y
          + (b * BF G x y + b * d * QF G y) := by
      rw [(hBsymm x y).1]
      field_simp
      linear_combination (BF G y x + d * QF G y) * hdet
    rw [key, etadd, etint _ ((hb.mul ((hint x hx).2 y hyL)).add ((hb.mul hd).mul (hint y hyL).1)),
      mul_one, etadd, etadd]
  · have h0 : oneL y = 0 := by simp [oneL, hyL]
    rw [h0, zero_mul]
    obtain ⟨w, hw, hnot⟩ : ∃ w ∈ dualL F G, et (BF G y w) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hyL (hdd y (fun ν hν => (etiff _).1 (hcon ν hν)))
    have hs : c • w ∈ aL κ (1 : F) := (hB1 _).2 (hcw w hw)
    have hf : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
        et (a / c * QF G (x + m)) * et (BF G y (x + m) / c)
          = et (a / c * QF G x) * et (BF G y x / c) := by
      intro x hx m hm
      rw [hg x hx m hm]
      congr 1
      obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
      rw [hBlin y x c l]
      have e : (BF G y x + c * BF G y l) / c = BF G y x / c + BF G y l := by
        field_simp
      rw [e, etadd, hdualet y hy l hl, mul_one]
    have h := sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x) * et (BF G y x / c)) hf (c • w) hs
    have hmul : ∑ x ∈ T, et (a / c * QF G (x + c • w)) * et (BF G y (x + c • w) / c)
        = et (BF G y w) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hxT
      have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
      rw [hexp, hBlin]
      have e1 : a / c * (QF G x + c * BF G x w + c ^ 2 * QF G w)
          = a / c * QF G x + (a * BF G x w + a * c * QF G w) := by
        field_simp
        ring
      have e2 : (BF G y x + c * BF G y w) / c = BF G y x / c + BF G y w := by
        field_simp
      rw [e1, e2, etadd, etadd, etadd, haB x hx w hw, etint _ (hcQ w hw)]
      ring
    have hsum : ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
      rw [hmul] at h
      have h5 : (et (BF G y w) - 1) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
        rw [sub_mul, h, one_mul, sub_self]
      exact (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hnot)
    rw [hsum, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.lattice_gaussSum_twist_dual_eq_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | exact GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | (intros; apply GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift <;> assumption)
end
