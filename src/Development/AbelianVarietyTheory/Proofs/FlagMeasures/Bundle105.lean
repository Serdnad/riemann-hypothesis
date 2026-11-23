module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.RegInv

theorem hpk_isUnit_det (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, GBasic.Hpk_sq, Matrix.det_one]
  exact ⟨⟨_, _, h, h⟩, rfl⟩

private lemma unit_lemma' {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : IsUnit γ.det ∧ γ⁻¹ ∈ GG k r :=
  (unitary_group_holds _ (Hpk k r) (hpk_isUnit_det k r)).2.2 γ h

theorem inv_mem {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : γ⁻¹ ∈ GG k r := (unit_lemma' h).2

private lemma herm_mulVec_eq_of_mem_GG {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ *ᵥ x) (γ *ᵥ y) = herm (Hpk k r) x y := by
  have hγ : γᴴ * Hpk k r * γ = Hpk k r := h
  simp only [herm]
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hγ]

private lemma herm_Hpk_swap (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]

theorem herm_inv {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ⁻¹ *ᵥ v) w = star (herm (Hpk k r) (γ *ᵥ w) v) := by
  have hv : γ *ᵥ (γ⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_lemma' h).1, Matrix.one_mulVec]
  rw [← herm_mulVec_eq_of_mem_GG h (γ⁻¹ *ᵥ v) w, hv]
  exact herm_Hpk_swap k r _ _

theorem zhat_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  unfold Formalism.QuantumDeterminants.Zhat
  exact herm_inv h _ _

theorem dmin_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r)
    (l : Fin (r + 2)) : Dmin k r z' z γ⁻¹ l = star (Dmin k r z z' γ l) := by
  simp only [Dmin]
  rw [zhat_inv z z' h, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

theorem gf_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Gf k r z' z γ⁻¹ = Gf k r z z' γ := by
  simp only [Gf, dmin_inv z z' h, Complex.star_def, Complex.normSq_conj]
  ring

theorem zhat_inv_and_reg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  refine ⟨zhat_inv z z' h, ?_⟩
  simp only [Greg, Set.mem_ofPred_eq, dmin_inv z z' h, gf_inv z z' h, star_ne_zero, h, inv_mem h,
    true_and]

end GlobalTheory.SgInf.RegInv
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IwaInt

variable {n : ℕ}

def crd (p : Fin n × Fin n × Bool → Prop) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ({t // p t} → ℝ) where
  toFun x t := if t.1.2.2 then (x t.1.1 t.1.2.1).im else (x t.1.1 t.1.2.1).re
  map_add' x y := by
    funext t; by_cases h : t.1.2.2 <;> simp [h]
  map_smul' a x := by
    funext t; by_cases h : t.1.2.2 <;> simp [h]

def emb (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] :
    ({t // p t} → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := Matrix.of fun i j =>
    ⟨if h : p (i, j, false) then v ⟨_, h⟩ else 0, if h : p (i, j, true) then v ⟨_, h⟩ else 0⟩
  map_add' x y := by
    ext i j
    apply Complex.ext <;> simp <;> split_ifs <;> simp
  map_smul' a x := by
    ext i j
    apply Complex.ext <;> simp

def Lc (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (x : Matrix (Fin n) (Fin n) ℂ) :
    ({t // p t} → ℝ) →ₗ[ℝ] ({t // p t} → ℝ) :=
  crd p ∘ₗ LinearMap.mulLeft ℝ x ∘ₗ emb p

def Rc (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (x : Matrix (Fin n) (Fin n) ℂ) :
    ({t // p t} → ℝ) →ₗ[ℝ] ({t // p t} → ℝ) :=
  crd p ∘ₗ LinearMap.mulRight ℝ x ∘ₗ emb p

abbrev pV (ε : Fin n → Bool) (t : Fin n × Fin n × Bool) : Prop := ε t.1 = ε t.2.1

abbrev pW (ε : Fin n → Bool) (t : Fin n × Fin n × Bool) : Prop :=
  ε t.1 = ε t.2.1 ∧ (t.2.1 < t.1 ∨ (t.1 = t.2.1 ∧ t.2.2 = false))

lemma crd_emb (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (v : {t // p t} → ℝ) :
    crd p (emb p v) = v := by
  funext ⟨⟨i, j, s⟩, h⟩
  cases s <;> simp [crd, emb, h]

lemma emb_crd_iff (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (x : Matrix (Fin n) (Fin n) ℂ) :
    emb p (crd p x) = x ↔ ∀ i j, (¬ p (i, j, false) → (x i j).re = 0) ∧ (¬ p (i, j, true) → (x i j).im = 0) := by
  constructor
  · intro h i j
    have h1 := congrFun (congrFun h i) j
    constructor
    · intro hp
      rw [← h1]; simp [emb, hp]
    · intro hp
      rw [← h1]; simp [emb, hp]
  · intro h
    ext i j
    apply Complex.ext
    · by_cases hp : p (i, j, false)
      · simp [emb, crd, hp]
      · simp [emb, hp, (h i j).1 hp]
    · by_cases hp : p (i, j, true)
      · simp [emb, crd, hp]
      · simp [emb, hp, (h i j).2 hp]

lemma comm_J_iff (ε : Fin n → Bool) (x : Matrix (Fin n) (Fin n) ℂ) :
    x * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * x ↔ ∀ i j, ε i ≠ ε j → x i j = 0 := by
  unfold Formalism.REAL.Jm
  constructor
  · intro h i j hij
    have h1 := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    cases hi : ε i <;> cases hj : ε j <;> simp [hi, hj] at h1 hij
    · linear_combination (1 / 2 : ℂ) * h1
    · linear_combination (-1 / 2 : ℂ) * h1
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : ε i = ε j
    · rw [hij, mul_comm]
    · rw [h i j hij]; simp

lemma isLo_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) (hb : IsLo b) : IsLo (a * b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i < k
  · rw [ha i k hk, zero_mul]
  · rw [hb k j (lt_of_le_of_lt (not_lt.1 hk) hij), mul_zero]

lemma isLo_mul_diag {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) (hb : IsLo b) (i : Fin n) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hb k i h, mul_zero]
  · rw [ha i k h, zero_mul]

lemma isLo_inv {a : (Matrix (Fin n) (Fin n) ℂ)ˣ} (ha : IsLo (a : Matrix (Fin n) (Fin n) ℂ)) :
    IsLo ((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  have hb : Matrix.BlockTriangular (a : Matrix (Fin n) (Fin n) ℂ) (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) :=
    fun i j h => ha i j h
  letI : Invertible (a : Matrix (Fin n) (Fin n) ℂ) := a.invertible
  have h2 := Matrix.blockTriangular_inv_of_blockTriangular hb
  rw [Matrix.coe_units_inv]
  exact fun i j h => h2 h

def GC (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g}
  mul_mem' := by
    intro g h hg hh
    have hg' : Commute (g : Matrix (Fin n) (Fin n) ℂ) (Formalism.REAL.Jm ε) := hg
    have hh' : Commute (h : Matrix (Fin n) (Fin n) ℂ) (Formalism.REAL.Jm ε) := hh
    exact hg'.mul_left hh'
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    have hg' : Commute (g : Matrix (Fin n) (Fin n) ℂ) (Formalism.REAL.Jm ε) := hg
    exact hg'.units_inv_left

def BC (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | g ∈ GC ε ∧ IsLo (g : Matrix (Fin n) (Fin n) ℂ) ∧ ∀ l, 0 < (g : Matrix (Fin n) (Fin n) ℂ) l l}
  mul_mem' := by
    intro g h hg hh
    refine ⟨mul_mem hg.1 hh.1, isLo_mul hg.2.1 hh.2.1, fun l => ?_⟩
    rw [Units.val_mul, isLo_mul_diag hg.2.1 hh.2.1]
    exact mul_pos (hg.2.2 l) (hh.2.2 l)
  one_mem' := ⟨one_mem _, fun i j h => by simp [Matrix.one_apply, h.ne], fun l => by simp⟩
  inv_mem' := by
    intro g hg
    refine ⟨inv_mem hg.1, isLo_inv hg.2.1, fun l => ?_⟩
    have h1 := isLo_mul_diag hg.2.1 (isLo_inv hg.2.1) l
    rw [Units.mul_inv, Matrix.one_apply_eq] at h1
    rw [← inv_eq_of_mul_eq_one_right h1.symm]
    exact inv_pos.2 (hg.2.2 l)

lemma isEmbedding_val : Topology.IsEmbedding
    (Units.val : (Matrix (Fin n) (Fin n) ℂ)ˣ → Matrix (Fin n) (Fin n) ℂ) := by
  refine Units.isEmbedding_val_mk' (f := fun x => x⁻¹) ?_ (fun u => (Matrix.coe_units_inv u).symm)
  intro x hx
  refine (continuousAt_matrix_inv x ?_).continuousWithinAt
  have h : x.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det x).1 hx).ne_zero
  have := NormedRing.inverse_continuousAt (Units.mk0 _ h)
  simpa using this

instance instSecondCountableSub (Γ : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : SecondCountableTopology Γ := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isEmbedding_val.comp Topology.IsEmbedding.subtypeVal).isInducing.secondCountableTopology

instance instMeasGC (ε : Fin n → Bool) : MeasurableSpace (GC ε) := borel _
instance instBorelGC (ε : Fin n → Bool) : BorelSpace (GC ε) := ⟨rfl⟩
instance instMeasBC (ε : Fin n → Bool) : MeasurableSpace (BC ε) := borel _
instance instBorelBC (ε : Fin n → Bool) : BorelSpace (BC ε) := ⟨rfl⟩

end GlobalTheory.IwaInt
end
end

section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec.KCIdent


open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder in
theorem exists_herm_log {n : ℕ} (y J : Matrix (Fin n) (Fin n) ℂ) (hy : IsUnit y)
    (hJ : Commute (yᴴ * y) J) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ, Lᴴ = L ∧ Commute L J ∧ NormedSpace.exp L = yᴴ * y := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ yᴴ * y := star_mul_self_nonneg y
  have hu : IsUnit (yᴴ * y) := hy.star.mul hy
  have hsp : IsStrictlyPositive (yᴴ * y) := IsStrictlyPositive.iff_of_unital.mpr ⟨h0, hu⟩
  refine ⟨CFC.log (yᴴ * y), ?_, Commute.cfc_real hJ Real.log, CFC.exp_log (yᴴ * y) hsp⟩
  exact (IsSelfAdjoint.log : IsSelfAdjoint (CFC.log (yᴴ * y)))

theorem differentiable_exp_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ (fun z : ℂ => NormedSpace.exp (z • X) i j) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  intro z
  have hz : DifferentiableAt ℂ (fun w : ℂ => NormedSpace.exp (w • X)) z :=
    (hasDerivAt_exp_smul_const (𝕂 := ℂ) X z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiableAt.comp z hz

theorem eq_zero_on_KC_of_eq_zero_on_Kset : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : Matrix (Fin n) (Fin n) ℂ → E), DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => F (Matrix.of y)) {y | Matrix.of y ∈ GlobalTheory.Dec.KC ε} → (∀ k ∈ Formalism.REAL.Kset ε, F k = 0) → ∀ y ∈ GlobalTheory.Dec.KC ε, F y = 0 := by
  intro n ε E _ _ _ F hF hK y hy
  unfold GlobalTheory.Dec.KC at hy
  obtain ⟨hyu, hyJ⟩ := hy
  have hJh : (Jm ε)ᴴ = Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hyhJ : yᴴ * Jm ε = Jm ε * yᴴ := by
    have h := congrArg Matrix.conjTranspose hyJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hc : Commute (yᴴ * y) (Jm ε) := by
    show yᴴ * y * Jm ε = Jm ε * (yᴴ * y)
    rw [mul_assoc, hyJ, ← mul_assoc, hyhJ, mul_assoc]
  obtain ⟨L, hLh, hLJ, hLe⟩ := exists_herm_log y (Jm ε) hyu hc
  obtain ⟨E', hE'⟩ : ∃ f : ℂ → Matrix (Fin n) (Fin n) ℂ, f = fun w => NormedSpace.exp (w • L) :=
    ⟨_, rfl⟩
  have hmul : ∀ a b : ℂ, E' a * E' b = E' (a + b) := by
    intro a b
    simp only [hE', add_smul]
    exact (Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left a).smul_right b)).symm
  have hstar : ∀ w : ℂ, (E' w)ᴴ = E' (star w) := by
    intro w
    simp only [hE']
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hLh]
  have hEJ : ∀ w : ℂ, E' w * Jm ε = Jm ε * E' w := by
    intro w
    simp only [hE']
    exact (hLJ.smul_left w).exp_left.eq
  have hE0 : E' 0 = 1 := by simp [hE']
  have hEone : E' 1 = yᴴ * y := by
    simp only [hE', one_smul]
    exact hLe
  have hEu : ∀ w : ℂ, IsUnit (E' w) := by
    intro w
    simp only [hE']
    exact Matrix.isUnit_exp _
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ, u = y * E' (-(1 / 2)) := ⟨_, rfl⟩
  have hhalf : star (-(1 / 2 : ℂ)) = -(1 / 2) := by simp
  have hu1 : uᴴ * u = 1 := by
    rw [hu, Matrix.conjTranspose_mul, hstar, hhalf]
    have e1 : E' (-(1 / 2)) * yᴴ * (y * E' (-(1 / 2))) = E' (-(1 / 2)) * (yᴴ * y) * E' (-(1 / 2)) := by
      simp only [mul_assoc]
    have e2 : (-(1 / 2 : ℂ) + 1 + -(1 / 2)) = 0 := by ring
    rw [e1, ← hEone, hmul, hmul, e2, hE0]
  have huJ : u * Jm ε = Jm ε * u := by
    rw [hu, mul_assoc, hEJ, ← mul_assoc, hyJ, mul_assoc]
  have huU : IsUnit u := by
    rw [hu]
    exact hyu.mul (hEu _)
  have hKC : ∀ z : ℂ, u * E' z ∈ GlobalTheory.Dec.KC ε := by
    intro z
    unfold GlobalTheory.Dec.KC
    refine ⟨huU.mul (hEu z), ?_⟩
    rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hzero : ∀ t : ℝ, F (u * E' ((t : ℂ) * Complex.I)) = 0 := by
    intro t
    apply hK
    unfold Formalism.REAL.Kset
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hstar]
      have hsw : star ((t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
        rw [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [mul_assoc, ← mul_assoc uᴴ, hu1, one_mul, hmul, hsw, hE0]
    · rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hγ : Differentiable ℂ (fun z : ℂ => (fun a b => (u * E' z) a b : Fin n → Fin n → ℂ)) := by
    refine differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    have hd : ∀ c, Differentiable ℂ (fun z : ℂ => E' z c b) := by
      intro c
      simp only [hE']
      exact differentiable_exp_entry L c b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun c _ => (differentiable_const (u a c)).mul (hd c)
  have hg : Differentiable ℂ (fun z : ℂ => F (u * E' z)) := fun z =>
    ((hF _ (hKC z)).comp z ((hγ z).differentiableWithinAt (s := Set.univ))
      (fun w _ => hKC w)).differentiableAt Filter.univ_mem
  have han : AnalyticOnNhd ℂ (fun z : ℂ => F (u * E' z)) Set.univ := fun z _ => hg.analyticAt z
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, F (u * E' z) = 0 := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhdsWithin (0 : ℂ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hcont : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Complex.I_ne_zero] using ht
    exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero))
  have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq
  have h12 := hall (Set.mem_univ (1 / 2 : ℂ))
  have hy' : u * E' (1 / 2) = y := by
    have e3 : (-(1 / 2 : ℂ) + 1 / 2) = 0 := by ring
    rw [hu, mul_assoc, hmul, e3, hE0, mul_one]
  simp only [Pi.zero_apply] at h12
  rw [hy'] at h12
  exact h12

end GlobalTheory.Dec.KCIdent
end

section

open GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.globalRankNumberBounds_size_comparisons : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧ max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧ Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧ (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  first | exact @GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | exact GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | (intros; apply GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes <;> assumption)
end

section

open GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧ Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧ C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  first | exact @GlobalTheory.Diag.PG.rankNums_first_half | exact GlobalTheory.Diag.PG.rankNums_first_half | (intros; apply GlobalTheory.Diag.PG.rankNums_first_half <;> assumption)
end

section

open NumberField

namespace GlobalTheory.RowLatXS

private theorem coefX_add_flag_measures {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) {x y : S.V}
    (hx : x ∈ Submodule.span E (Set.range F.e)) (hy : y ∈ Submodule.span E (Set.range F.e)) :
    F.coefX (x + y) a = F.coefX x a + F.coefX y a := by
  have hxy : x + y ∈ Submodule.span E (Set.range F.e) := Submodule.add_mem _ hx hy
  unfold Formalism.MainNotions.S.FlagG.coefX
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hxy]
  have hsum : (⟨x + y, hxy⟩ : Submodule.span E (Set.range F.e)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [hsum, map_add (f := _), Finsupp.add_apply]

private theorem coefX_smul_flag_measures {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) (c : E) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range F.e)) :
    F.coefX (c • x) a = c * F.coefX x a := by
  have hcx : c • x ∈ Submodule.span E (Set.range F.e) := Submodule.smul_mem _ c hx
  unfold Formalism.MainNotions.S.FlagG.coefX
  rw [dite_eq_left hx, dite_eq_left hcx]
  have hprod : (⟨c • x, hcx⟩ : Submodule.span E (Set.range F.e)) = c • ⟨x, hx⟩ := rfl
  rw [hprod, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem Ia_fg_and_mem_iff {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ)
    (T : E) (F : Formalism.MainNotions.S.FlagG S r T) (Λ : Submodule (𝓞 E) S.V) (a : Fin r) (hΛ : Λ.FG) :
    (GlobalTheory.RowLatXS.Ia Λ F a).FG ∧ ∀ t : E, t ∈ GlobalTheory.RowLatXS.Ia Λ F a ↔
      ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
  classical
  have hXle : F.Xa (a.val + 1) ≤ Submodule.span E (Set.range F.e) := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    exact Submodule.span_mono (Set.image_subset_range _ _)

  let W : Submodule (𝓞 E) S.V := Λ ⊓ (F.Xa (a.val + 1)).restrictScalars (𝓞 E)
  have hmem : ∀ x : W, (x : S.V) ∈ Submodule.span E (Set.range F.e) := fun x =>
    hXle ((Submodule.restrictScalars_mem _ _ _).1 (Submodule.mem_inf.1 x.2).2)
  let g : W →ₗ[𝓞 E] E :=
    { toFun := fun x => F.coefX (x : S.V) a
      map_add' := fun x y => coefX_add_flag_measures F a (hmem x) (hmem y)
      map_smul' := fun c x => by
        change F.coefX (c • (x : S.V)) a = c • F.coefX (x : S.V) a
        rw [← algebraMap_smul E c (x : S.V), coefX_smul_flag_measures F a _ (hmem x), Algebra.smul_def] }
  have hrange : ∀ t : E, t ∈ LinearMap.range g ↔
      ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
    intro t
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (Submodule.mem_inf.1 x.2).1, (Submodule.mem_inf.1 x.2).2, rfl⟩
    · rintro ⟨x, hx, hxa, rfl⟩
      exact ⟨⟨x, Submodule.mem_inf.2 ⟨hx, hxa⟩⟩, rfl⟩

  have hIa : GlobalTheory.RowLatXS.Ia Λ F a = LinearMap.range g := by
    unfold GlobalTheory.RowLatXS.Ia
    apply le_antisymm
    · rw [Submodule.span_le]
      intro t ht
      exact (hrange t).2 ht
    · intro t ht
      exact Submodule.subset_span ((hrange t).1 ht)
  refine ⟨?_, fun t => by rw [hIa]; exact hrange t⟩

  have : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  have : IsNoetherian (𝓞 E) W := isNoetherian_of_le inf_le_left
  rw [hIa, LinearMap.range_eq_map]
  exact (IsNoetherian.noetherian (⊤ : Submodule (𝓞 E) W)).map g

end GlobalTheory.RowLatXS
end
