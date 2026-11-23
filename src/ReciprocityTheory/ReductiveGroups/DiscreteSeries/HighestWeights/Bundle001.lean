module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if ε a = ε b then Z a b else 0

theorem cpart1_bdPart_apply (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    cpart1 ε (bdPart ε Z) a b = if ε a = ε b then (Z a b - star (Z b a)) / 2 else 0 := by
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [cpart1, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring

theorem cpart2_bdPart_apply (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    cpart2 ε (bdPart ε Z) a b = if ε a = ε b then -Complex.I * (Z a b + star (Z b a)) / 2 else 0 := by
  have hI : (1 / (2 * Complex.I)) = -Complex.I / 2 := by
    rw [one_div, mul_inv, Complex.inv_I]; ring
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [cpart2, hI, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring

theorem inK_apply (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (a b : Fin n) :
    (ε a ≠ ε b → X a b = 0) ∧ star (X b a) = - X a b := by
  have h1 := congrFun (congrFun hX.1 a) b
  have h2 := congrFun (congrFun hX.2 a) b
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] at h1 h2 ⊢
  all_goals first
    | exact ⟨by linear_combination h2 / 2, by linear_combination h1 + h2⟩
    | exact ⟨by linear_combination -h2 / 2, by linear_combination -h1 - h2⟩
    | linear_combination h1 | linear_combination -h1

theorem inK_cpart1_bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart1 ε (bdPart ε Z)) := by
  refine ⟨?_, ?_⟩ <;> ext a b <;>
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply,
      cpart1_bdPart_apply, Matrix.zero_apply] <;>
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring

theorem inK_cpart2_bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart2 ε (bdPart ε Z)) := by
  refine ⟨?_, ?_⟩ <;> ext a b <;>
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply,
      cpart2_bdPart_apply, Matrix.zero_apply] <;>
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring

theorem cpart_bdPart_of_inK (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    cpart1 ε (bdPart ε X) = X ∧ cpart2 ε (bdPart ε X) = 0 := by
  refine ⟨?_, ?_⟩ <;> ext a b
  · obtain ⟨h0, hs⟩ := inK_apply ε hX a b
    rw [cpart1_bdPart_apply]
    split_ifs with h
    · rw [hs]; ring
    · exact (h0 h).symm
  · obtain ⟨h0, hs⟩ := inK_apply ε hX a b
    rw [Matrix.zero_apply, cpart2_bdPart_apply]
    split_ifs with h
    · rw [hs]; ring
    · rfl

theorem cpart1_bdPart_add (ε : Fin n → Bool) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (bdPart ε (Z + Z')) = cpart1 ε (bdPart ε Z) + cpart1 ε (bdPart ε Z') := by
  ext a b
  simp only [Matrix.add_apply, cpart1_bdPart_apply, star_add]
  split_ifs <;> ring

theorem cpart2_bdPart_add (ε : Fin n → Bool) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (bdPart ε (Z + Z')) = cpart2 ε (bdPart ε Z) + cpart2 ε (bdPart ε Z') := by
  ext a b
  simp only [Matrix.add_apply, cpart2_bdPart_apply, star_add]
  split_ifs <;> ring

theorem cpart1_bdPart_smul (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (bdPart ε (c • Z)) =
      ((c.re : ℝ) : ℂ) • cpart1 ε (bdPart ε Z) + ((-c.im : ℝ) : ℂ) • cpart2 ε (bdPart ε Z) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']
  split_ifs
  · apply Complex.ext <;> simp <;> ring
  · simp

theorem cpart2_bdPart_smul (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (bdPart ε (c • Z)) =
      ((c.im : ℝ) : ℂ) • cpart1 ε (bdPart ε Z) + ((c.re : ℝ) : ℂ) • cpart2 ε (bdPart ε Z) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']
  split_ifs
  · apply Complex.ext <;> simp <;> ring
  · simp

theorem inK_ofReal_smul (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (r : ℝ) :
    inK ε ((r : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := hX
  have hr : star (r : ℂ) = r := by simp
  constructor
  · change ((r : ℂ) • X)ᴴ * Jm ε + Jm ε * ((r : ℂ) • X) = 0
    change Xᴴ * Jm ε + Jm ε * X = 0 at h1
    rw [conjTranspose_smul, hr, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]

section Op

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def RLinOnK (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) : Prop :=
  ∀ (X Y : Matrix (Fin n) (Fin n) ℂ) (r : ℝ), inK ε X → inK ε Y →
    A (X + Y) = A X + A Y ∧ A ((r : ℂ) • X) = (r : ℂ) • A X

def cext (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    V →L[ℂ] V :=
  A (cpart1 ε (bdPart ε Z)) + Complex.I • A (cpart2 ε (bdPart ε Z))

theorem smul_combo (c : ℂ) (u v : V →L[ℂ] V) :
    ((c.re : ℝ) : ℂ) • u + ((-c.im : ℝ) : ℂ) • v + Complex.I • (((c.im : ℝ) : ℂ) • u + ((c.re : ℝ) : ℂ) • v) =
      c • (u + Complex.I • v) := by
  have hc : (c.re : ℂ) + c.im * Complex.I = c := Complex.re_add_im c
  push_cast
  linear_combination (norm := module) hc • (u + Complex.I • v) - ((c.im : ℂ) * Complex.I_sq) • v

theorem cext_add (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    (Z Z' : Matrix (Fin n) (Fin n) ℂ) : cext ε A (Z + Z') = cext ε A Z + cext ε A Z' := by
  unfold cext
  rw [cpart1_bdPart_add, cpart2_bdPart_add,
    (hA _ _ 0 (inK_cpart1_bdPart ε Z) (inK_cpart1_bdPart ε Z')).1,
    (hA _ _ 0 (inK_cpart2_bdPart ε Z) (inK_cpart2_bdPart ε Z')).1, smul_add]
  abel

theorem cext_smul (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : cext ε A (c • Z) = c • cext ε A Z := by
  have hP := inK_cpart1_bdPart ε Z
  have hQ := inK_cpart2_bdPart ε Z
  unfold cext
  rw [cpart1_bdPart_smul, cpart2_bdPart_smul,
    (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1,
    (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1,
    (hA _ _ c.re hP hP).2, (hA _ _ (-c.im) hQ hQ).2, (hA _ _ c.im hP hP).2, (hA _ _ c.re hQ hQ).2]
  exact smul_combo c _ _

theorem cext_of_inK (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : cext ε A X = A X := by
  obtain ⟨h1, h2⟩ := cpart_bdPart_of_inK ε hX
  have h0 : A 0 = 0 := by
    have := (hA X X 0 hX hX).2
    simpa using this
  unfold cext
  rw [h1, h2, h0, smul_zero, add_zero]

def cextL (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hA : RLinOnK ε A) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V) where
  toFun := cext ε A
  map_add' := cext_add ε hA
  map_smul' := cext_smul ε hA

theorem cextL_apply (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hA : RLinOnK ε A)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cextL ε A hA Z = cext ε A Z := rfl

end Op

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma twist_det_star_mul {ε : Fin n → Bool} (k : KG ε) : star (toMK k).det * (toMK k).det = 1 := by
  obtain ⟨hu, -⟩ := k.2
  calc star (toMK k).det * (toMK k).det = (star (toMK k)).det * (toMK k).det := by
        rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    _ = (star (toMK k) * toMK k).det := (Matrix.det_mul _ _).symm
    _ = 1 := by
        rw [show star (toMK k) * toMK k = 1 from Unitary.star_mul_self_of_mem hu, Matrix.det_one]

lemma twist_det_ne {ε : Fin n → Bool} (k : KG ε) : (toMK k).det ≠ 0 := by
  intro h
  have h1 := twist_det_star_mul k
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

lemma twist_toMK_inj {ε : Fin n → Bool} {k k' : KG ε} (h : toMK k = toMK k') : k = k' :=
  Subtype.ext (Subtype.ext (Units.ext h))

private theorem hasDerivAt_exp_smul_apply_zero (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : ∀ t : ℝ, ((t : ℂ) • X) = t • X := fun t => Complex.coe_smul t X
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [hc]
  exact h2

lemma twist_hasDerivAt_det_exp (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det) X.trace 0 := by
  refine InhabA.hasDerivAt_det_of_one (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X ?_
    (fun i j => hasDerivAt_exp_smul_apply_zero X i j)
  simp

lemma twist_smul_mem_unitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {s : ℂ}
    (hs : star s * s = 1) {A : V →L[ℂ] V} (hA : A ∈ unitary (V →L[ℂ] V)) :
    s • A ∈ unitary (V →L[ℂ] V) := by
  exact Unitary.smul_mem_of_mem (Unitary.mem_iff.2 ⟨hs, by rw [mul_comm]; exact hs⟩) hA

lemma twist_zpow_star {ε : Fin n → Bool} (k : KG ε) (c : ℤ) :
    star ((toMK k).det ^ c) * (toMK k).det ^ c = 1 := by
  rw [star_zpow₀, ← _root_.mul_zpow, twist_det_star_mul, _root_.one_zpow]

theorem kType_twist {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) :
    Nonempty (KType ε (fun a => Λ a + (c : ℝ))) := by
  letI := T.instNACG
  letI := T.instIPS
  letI := T.instFD
  letI := T.instCS
  let d : KG ε → ℂ := fun k => (toMK k).det ^ c
  have hd : ∀ k, star (d k) * d k = 1 := fun k => twist_zpow_star k c
  have hdne : ∀ k, d k ≠ 0 := fun k => zpow_ne_zero c (twist_det_ne k)
  have hdmul : ∀ k k', d (k * k') = d k * d k' := by
    intro k k'
    show (toMK (k * k')).det ^ c = (toMK k).det ^ c * (toMK k').det ^ c
    rw [show toMK (k * k') = toMK k * toMK k' from rfl, Matrix.det_mul, _root_.mul_zpow]
  have hd1 : d 1 = 1 := by
    show (toMK (1 : KG ε)).det ^ c = 1
    rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.det_one, _root_.one_zpow]
  let τ' : KG ε →* unitary (T.V →L[ℂ] T.V) :=
    { toFun := fun k => ⟨d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V),
        twist_smul_mem_unitary (hd k) (T.τ k).2⟩
      map_one' := by
        apply Subtype.ext
        show d 1 • ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
        rw [hd1, one_smul, map_one, OneMemClass.coe_one]
      map_mul' := fun k k' => by
        apply Subtype.ext
        show d (k * k') • ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) =
          (d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) *
            (d k' • ((T.τ k' : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
        rw [hdmul, map_mul, Submonoid.coe_mul, smul_mul_smul_comm] }
  have hcontd : Continuous d := by
    have h1 : Continuous fun k : KG ε => (toMK k).det :=
      Continuous.matrix_det (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))
    exact h1.zpow₀ c (fun k => Or.inl (twist_det_ne k))
  let dτ' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T.V →L[ℂ] T.V) :=
    T.dτ + (c : ℂ) • (Matrix.traceLinearMap (Fin n) ℂ ℂ).smulRight (1 : T.V →L[ℂ] T.V)
  have hdτ : ∀ X, dτ' X = T.dτ X + ((c : ℂ) * X.trace) • (1 : T.V →L[ℂ] T.V) := by
    intro X
    simp only [dτ', LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply, smul_smul]
  refine ⟨⟨T.V, τ', ?_, ?_, dτ', ?_, T.w, T.w_norm, ?_, ?_⟩⟩
  · show Continuous (fun k => (⟨d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V),
        twist_smul_mem_unitary (hd k) (T.τ k).2⟩ : unitary (T.V →L[ℂ] T.V)))
    exact Continuous.subtype_mk (hcontd.smul (continuous_subtype_val.comp T.cont)) _
  · intro W hW
    refine T.irred W (fun k v hv => ?_)
    have h : (d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) v ∈ W := hW k v hv
    have e : ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v =
        (d k)⁻¹ • ((d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) v) := by
      rw [ContinuousLinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (hdne k), one_smul]
    rw [e]
    exact W.smul_mem _ h
  · intro X hX γ hγ
    have hg := T.hasDeriv X hX γ hγ
    have hγ0 : γ 0 = 1 := by
      apply twist_toMK_inj
      rw [hγ 0, show (((0 : ℝ) : ℂ) • X) = 0 by simp, NormedSpace.exp_zero]
      rfl
    have hf0 : HasDerivAt (fun t : ℝ => (toMK (γ t)).det) X.trace 0 := by
      refine (twist_hasDerivAt_det_exp X).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))
      simp only [hγ t]
    have hdet0 : (toMK (γ 0)).det = 1 := by
      rw [hγ0]
      exact Matrix.det_one
    have hf : HasDerivAt (fun t : ℝ => d (γ t)) ((c : ℂ) * X.trace) 0 := by
      have hz := hasDerivAt_zpow c ((toMK (γ 0)).det) (Or.inl (twist_det_ne _))
      have hc := hz.comp (0 : ℝ) hf0
      rw [hdet0, _root_.one_zpow, mul_one] at hc
      exact hc
    have hτ0 : ((T.τ (γ 0) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1 := by
      rw [hγ0, map_one, OneMemClass.coe_one]
    have hd0 : d (γ 0) = 1 := by
      show (toMK (γ 0)).det ^ c = 1
      rw [hdet0, _root_.one_zpow]
    have hsm := hf.smul hg
    simp only [hτ0, hd0, one_smul] at hsm
    rw [← hdτ] at hsm
    exact hsm
  · intro a
    rw [hdτ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      T.w_wt a, Matrix.trace_single_eq_same, mul_one]
    push_cast
    rw [add_smul]
  · intro a b hab he
    rw [hdτ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      T.w_hw a b hab he, Matrix.trace_single_eq_of_ne _ _ _ hab.ne, mul_zero, zero_smul, add_zero]

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
