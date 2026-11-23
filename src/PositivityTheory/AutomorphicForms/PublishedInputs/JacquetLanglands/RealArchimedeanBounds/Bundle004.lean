module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle001
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
import Mathlib.Tactic.Lemma
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

namespace UpperTheory.Esk.IwasawaDecompositionLemmas

theorem ut_mul {R : Type} [CommRing R] {X Y : GL (Fin 2) R} (hX : (X : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hY : (Y : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) : ((X * Y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hX, hY]

theorem ut_eq {R : Type} [CommRing R] (p : GL (Fin 2) R) (h : (p : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (z t : Rˣ) (x : R), p = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff t x := by
  have hd : IsUnit ((p : Matrix (Fin 2) (Fin 2) R) 0 0 * (p : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    have := (Matrix.GeneralLinearGroup.det p).isUnit
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h, mul_zero, sub_zero] at this
  obtain ⟨a, ha⟩ := isUnit_of_mul_isUnit_left hd
  obtain ⟨d, hdd⟩ := isUnit_of_mul_isUnit_right hd
  refine ⟨d, a * d⁻¹, (p : Matrix (Fin 2) (Fin 2) R) 0 1 * ((d⁻¹ : Rˣ) : R), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, ha, hdd, h] <;>
    rw [← hdd, mul_left_comm, Units.mul_inv, mul_one]

def LK {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (m : GL (Fin 2) K) : Prop :=
  (∀ i j, v ((m : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1) ∧ ∀ i j, v (((m⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1

theorem LK_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : LK v 1 :=
  ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, fun i j => by fin_cases i <;> fin_cases j <;> simp⟩

theorem LK_mul {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m n : GL (Fin 2) K}
    (hm : LK v m) (hn : LK v n) : LK v (m * n) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hm.1 _ _) (hn.1 _ _)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hn.2 _ _) (hm.2 _ _)

theorem loc_iw {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (b : GL (Fin 2) K) :
    ∃ p k : GL (Fin 2) K, (p : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ LK v k ∧ b = p * k := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [Matrix.det_fin_two] at hdet
  set γ := (b : Matrix (Fin 2) (Fin 2) K) 1 0 with hγ
  set δ := (b : Matrix (Fin 2) (Fin 2) K) 1 1 with hδ
  by_cases h : v γ ≤ v δ
  · have hδ0 : δ ≠ 0 := by
      intro h0
      have h1 : γ = 0 := by
        rw [h0, map_zero] at h
        exact (Valuation.zero_iff v).1 (le_antisymm h zero_le)
      apply hdet; rw [h0, h1]; ring
    let k : GL (Fin 2) K := ⟨!![1, 0; γ / δ, 1], !![1, 0; -(γ / δ), 1],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩
    · change ((b : Matrix (Fin 2) (Fin 2) K) * !![1, 0; -(γ / δ), 1]) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [← hγ, ← hδ]
      field_simp
      ring
    · fin_cases i <;> fin_cases j <;> simp [k]
      exact div_le_one_of_le₀ h zero_le
    · change v ((!![1, 0; -(γ / δ), 1] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp
      exact div_le_one_of_le₀ h zero_le
  · have hlt : v δ < v γ := lt_of_not_ge h
    have hγ0 : γ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hlt
      exact not_lt_zero hlt
    let k : GL (Fin 2) K := ⟨!![0, 1; 1, δ / γ], !![-(δ / γ), 1; 1, 0],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩
    · change ((b : Matrix (Fin 2) (Fin 2) K) * !![-(δ / γ), 1; 1, 0]) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [← hγ, ← hδ]
      field_simp
      ring
    · fin_cases i <;> fin_cases j <;> simp [k]
      exact div_le_one_of_le₀ hlt.le zero_le
    · change v ((!![-(δ / γ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp
      exact div_le_one_of_le₀ hlt.le zero_le

section Fin

variable {F : Type} [Field F] [NumberField F]

theorem ev_int (x : Af F) : ∀ᶠ w in Filter.cofinite, Valued.v (pLoc F w x) ≤ 1 := by
  filter_upwards [x.2] with w hw
  exact hw

theorem ev_good (b : GL (Fin 2) (Af F)) :
    ∀ᶠ w in Filter.cofinite, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b) := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v (pLoc F w ((b : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => ev_int _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v (pLoc F w (((b⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => ev_int _
  filter_upwards [h1, h2] with w hw hw'
  refine ⟨fun i j => hw i j, fun i j => ?_⟩
  rw [← map_inv]
  exact hw' i j

theorem locGL_10 (w : HeightOneSpectrum (𝓞 F)) (p : GL (Fin 2) (w.adicCompletion F))
    (hp : (p : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0 = 0) :
    (locGL F 2 w p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 := by
  have key : ∀ v, pLoc F v ((locGL F 2 w p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0) = 0 := fun v => by
    change ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w p) : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
    by_cases hvw : v = w
    · subst hvw; rw [pLoc_locGL]; exact hp
    · rw [pLoc_locGL_of_ne hvw]; simp
  exact FiniteAdeleRing.ext _ fun v => (key v).trans (map_zero (pLoc F v)).symm

theorem iwasawa_decomposition_finite_adeles (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ b : GL (Fin 2) (Af F),
    (∀ w ∉ S, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b)) →
    ∃ p k : GL (Fin 2) (Af F), (p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 ∧
      (∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) ∧ b = p * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro b hb
    exact ⟨1, b, by simp, fun w => hb w (Finset.notMem_empty w), (one_mul b).symm⟩
  | insert w S hw ih =>
    intro b hb
    obtain ⟨pw, kw, hpw, hkw, e⟩ := loc_iw Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b)
    obtain ⟨p, k, hp, hk, e'⟩ := ih ((locGL F 2 w pw)⁻¹ * b * (locGL F 2 w kw)⁻¹) fun v hv => by
      by_cases hvw : v = w
      · subst hvw
        rw [map_mul, map_mul, map_inv, map_inv, pLoc_locGL, pLoc_locGL, e, inv_mul_cancel_left, mul_inv_cancel]
        exact LK_one _
      · rw [map_mul, map_mul, map_inv, map_inv, pLoc_locGL_of_ne hvw, pLoc_locGL_of_ne hvw, inv_one, one_mul,
          mul_one]
        exact hb v (by simp [hvw, hv])
    refine ⟨locGL F 2 w pw * p, k * locGL F 2 w kw, ut_mul (locGL_10 w pw hpw) hp, fun v => ?_, ?_⟩
    · rw [map_mul]
      refine LK_mul _ (hk v) ?_
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hkw
      · rw [pLoc_locGL_of_ne hvw]; exact LK_one _
    · rw [show locGL F 2 w pw * p * (k * locGL F 2 w kw) = locGL F 2 w pw * (p * k) * locGL F 2 w kw by
        simp only [mul_assoc], ← e']
      group

theorem fin_iw (b : GL (Fin 2) (Af F)) :
    ∃ p k : GL (Fin 2) (Af F), (p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 ∧
      (∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) ∧ b = p * k := by
  have hf := Filter.eventually_cofinite.1 (ev_good b)
  refine iwasawa_decomposition_finite_adeles hf.toFinset b fun w hw => ?_
  by_contra h
  exact hw (hf.mem_toFinset.2 h)

theorem mem_maximal_compact_of_local (h1 : ∀ g : GF F, g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F)
    (h2 : ∀ x : Af F, x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1) {k : GF F}
    (hk : ∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) : k ∈ K0 F := by
  refine (h1 k).2 ⟨fun i j => (h2 _).2 fun w => (hk w).1 i j, fun i j => (h2 _).2 fun w => ?_⟩
  have := (hk w).2 i j
  rw [← map_inv] at this
  exact this

end Fin

end UpperTheory.Esk.IwasawaDecompositionLemmas

open UpperTheory.Esk.IwasawaDecompositionLemmas in
theorem UpperTheory.Esk.aIw : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw := by
  intro hM F _ _ x
  obtain ⟨h1, h2, -⟩ := hM F
  obtain ⟨p, k, hp, hk, e⟩ := fin_iw x
  obtain ⟨z, t, u, hz⟩ := ut_eq p hp
  refine ⟨z, t, u, k, mem_maximal_compact_of_local h1 h2 hk, ?_⟩
  rw [e, hz]
  rfl
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.NearUnitLemmas

open scoped Classical

abbrev bU (F : Type) [Field F] [NumberField F] :=
  (NumberField.Units.basisUnitLattice F).ofZLatticeBasis ℝ (NumberField.Units.unitLattice F)

theorem abs_sg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |sg v x| = v x := by
  simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v) x

theorem near_unit (F : Type) [Field F] [NumberField F] (a : NumberField.Units.dirichletUnitTheorem.logSpace F) :
    ∃ x : (𝓞 F)ˣ, ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      |a w - InfinitePlace.mult w.1 * Real.log (w.1 (x : F))| ≤ ∑ i, ‖bU F i‖ := by
  have hmem : (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈
      NumberField.Units.unitLattice F := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (NumberField.Units.unitLattice F)
      (NumberField.Units.basisUnitLattice F)]
    exact (ZSpan.floor (bU F) a).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨x.toMul, fun w => ?_⟩
  have h1 : InfinitePlace.mult w.1 * Real.log (w.1 ((x.toMul : (𝓞 F)ˣ) : F)) =
      (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w := by
    rw [← hx]; rfl
  rw [h1]
  have h2 : a w - (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w =
      ZSpan.fract (bU F) a w := by rw [ZSpan.fract_apply]; rfl
  rw [h2, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ w).trans (ZSpan.norm_fract_le _ _)

end UpperTheory.Esk.NearUnitLemmas

namespace UpperTheory.Esk

open UpperTheory.Esk.NearUnitLemmas in
theorem aUnit : UpperTheory.Esk.AUnit := by
  classical
  intro F _ _ _
  set M : ℝ := ∑ i, ‖bU F i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨Real.exp (2 * (Fintype.card (InfinitePlace F) * M)), Real.exp_pos _, fun y hy => ?_⟩
  set L : InfinitePlace F → ℝ := fun w => Real.log |y w|
  set m : ℝ := (∑ w, L w) / Fintype.card (InfinitePlace F)
  obtain ⟨x, hx⟩ := near_unit F (fun w => m - L w.1)
  set u : F := (x : F)
  have hmult : ∀ w : InfinitePlace F, InfinitePlace.mult w = 1 :=
    fun w => (IsTotallyReal.isReal w).mult_eq_one
  set d : InfinitePlace F → ℝ := fun w => Real.log (w u) + L w - m
  have hn : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ w, d w = 0 := by
    have h0 : ∑ w : InfinitePlace F, Real.log (w u) = 0 := by
      simpa [hmult] using NumberField.Units.sum_mult_mul_log x
    simp only [d, Finset.sum_sub_distrib, Finset.sum_add_distrib, h0, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, m]
    field_simp
    ring
  have hne : ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| ≤ M := by
    intro w
    have := hx w
    rw [hmult, Nat.cast_one, one_mul] at this
    calc |d w| = |(m - L w.1) - Real.log (w.1 u)| := by
          rw [← abs_neg]; congr 1; simp only [d]; ring
      _ ≤ M := this
  have hall : ∀ w, |d w| ≤ Fintype.card (InfinitePlace F) * M := by
    intro w
    by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
    · subst hw
      have h := Fintype.sum_eq_add_sum_subtype_ne d NumberField.Units.dirichletUnitTheorem.w₀
      rw [hsum] at h
      have h' : d NumberField.Units.dirichletUnitTheorem.w₀ =
          -∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w := by
        linarith
      rw [h', abs_neg]
      calc |∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w|
          ≤ ∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, M :=
            Finset.sum_le_sum fun w _ => hne w
        _ = (Fintype.card {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} : ℝ) * M := by
            simp
        _ ≤ Fintype.card (InfinitePlace F) * M := by
            gcongr
            exact_mod_cast Fintype.card_subtype_le _
    · calc |d w| ≤ M := hne ⟨w, hw⟩
        _ ≤ Fintype.card (InfinitePlace F) * M := by
          have : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
          nlinarith
  have hu0 : ∀ w : InfinitePlace F, 0 < w u := fun w => NumberField.Units.pos_at_place x w
  have hval : ∀ w, |sg w u * y w| = Real.exp (d w + m) := by
    intro w
    simp only [d, L]
    rw [abs_mul, abs_sg, sub_add_cancel, Real.exp_add, Real.exp_log (hu0 w),
      Real.exp_log (abs_pos.2 (hy w))]
  refine ⟨u, ?_, ?_, ?_, fun v v' => ?_⟩
  · intro h
    have := hu0 NumberField.Units.dirichletUnitTheorem.w₀
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  · exact NumberField.RingOfIntegers.isIntegral_coe (x : 𝓞 F)
  · have : u⁻¹ = ((x⁻¹ : (𝓞 F)ˣ) : F) := by simp [u]
    rw [this]
    exact NumberField.RingOfIntegers.isIntegral_coe ((x⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  · rw [hval, hval, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (hall v)).2
    have h2 := (abs_le.1 (hall v')).1
    linarith

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.MonomialSupportLemmas

variable {F : Type} [Field F] [NumberField F]

theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.MonomialSupportLemmas

open UpperTheory.Esk.MonomialSupportLemmas in
theorem UpperTheory.Esk.aMono : UpperTheory.Esk.AMono := by
  intro F _ _ t t' h
  classical
  unfold absF
  set s := ((fin_supp t).union (fin_supp t')).toFinset
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) (by intro w hw; simp [s, hw]),
    finprod_eq_prod_of_mulSupport_subset _ (s := s) (by intro w hw; simp [s, hw])]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    fun w _ => (Valued.toNormedField.norm_le_iff).2 (h w)
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.BoxMapsToLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma place_eq (v : InfinitePlace F) (t : F) : v t = |sg v t| := by
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.norm_embedding_of_isReal _ t).symm

lemma injOn (R : ℝ) : Set.InjOn (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R} := by
  intro t ht t' ht' h
  by_contra hne
  let a : 𝓞 F := ⟨t - t', ht.1.sub ht'.1⟩
  have ha : a ≠ 0 := by
    intro h0
    apply hne
    have h1 : ((a : 𝓞 F) : F) = 0 := by rw [h0]; rfl
    exact sub_eq_zero.1 h1
  have hlt : ∀ v : InfinitePlace F, v (a : F) < 1 := by
    intro v
    have hv := congrFun h v
    simp only at hv
    rw [place_eq]
    show |sg v (t - t')| < 1
    rw [map_sub]
    exact Int.abs_sub_lt_one_of_floor_eq_floor hv
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

open Classical in
lemma mapsTo (R : ℝ) : Set.MapsTo (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R}
    ((Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ : Finset _) : Set _) := by
  intro t ht
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro v
  have h1 := ht.2 v
  rw [place_eq, abs_le] at h1
  have hc : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith [h1.1]
  · have h2 : ((⌊sg v t⌋ : ℤ) : ℝ) ≤ ((⌈R⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.floor_le (sg v t), h1.2]
    exact_mod_cast h2

end UpperTheory.Esk.BoxMapsToLemmas

open Classical in
theorem UpperTheory.Esk.dBox : UpperTheory.Esk.DBox := by
  intro F _ _ _
  refine ⟨5 ^ Fintype.card (InfinitePlace F), fun R hR => ?_⟩
  set d := Fintype.card (InfinitePlace F)
  set T := (Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊)
  refine ⟨Set.Finite.of_injOn (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn _ (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  have h2 : T.card = (2 * ⌈R⌉₊ + 1) ^ d := by
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  have h3 : ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * max 1 R := by
    have := Nat.ceil_lt_add_one hR
    have hm1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
    have hmR : R ≤ max 1 R := le_max_right _ _
    push_cast
    linarith
  have h4 : (max 1 R) ^ d ≤ 1 + R ^ d := by
    rcases le_total R 1 with h | h
    · rw [max_eq_left h, one_pow]
      linarith [pow_nonneg hR d]
    · rw [max_eq_right h]
      linarith [zero_le_one' ℝ]
  calc (_ : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h1
    _ = ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ^ d := by rw [h2]; push_cast; ring
    _ ≤ (5 * max 1 R) ^ d := pow_le_pow_left₀ (by positivity) h3 _
    _ = 5 ^ d * (max 1 R) ^ d := mul_pow _ _ _
    _ ≤ 5 ^ d * (1 + R ^ d) := mul_le_mul_of_nonneg_left h4 (by positivity)
end
end
