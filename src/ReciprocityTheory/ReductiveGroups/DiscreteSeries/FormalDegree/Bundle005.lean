module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbE (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def dpbP (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun W ab := (1 / 2 : ℝ) • (W ab.1.1 ab.1.2 + star (W ab.1.2 ab.1.1))
  map_add' W W' := by
    ext ab
    simp only [Matrix.add_apply, Pi.add_apply, star_add]
    module
  map_smul' c W := by
    ext ab
    simp only [Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, star_smul, star_trivial]
    module

theorem dpbP_herm {ε : Fin n → Bool} {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ = W) (ab : PCoord ε) :
    dpbP ε W ab = W ab.1.1 ab.1.2 := by
  have h : star (W ab.1.2 ab.1.1) = W ab.1.1 ab.1.2 := by
    have := congrFun (congrFun hW ab.1.1) ab.1.2
    simpa [Matrix.conjTranspose_apply] using this
  simp only [dpbP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, Complex.real_smul]
  push_cast
  ring

theorem dpbP_E {ε : Fin n → Bool} (w : PCoord ε → ℂ) : dpbP ε (dpbE ε w) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, hab, hne⟩ := ab
  have h1 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => absurd h.1 (not_lt.mpr hab.le)
  simp only [dpbP, dpbE, LinearMap.coe_mk, AddHom.coe_mk, pmat, dif_pos (And.intro hab hne), dif_neg h1,
    star_star]
  rw [Complex.real_smul]
  push_cast
  ring

theorem dpb_JWJ (ε : Fin n → Bool) (W : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * W * Jm ε) a b = if ε a = ε b then W a b else -W a b := by
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases ε a <;> cases ε b <;> simp

theorem dpbE_P {ε : Fin n → Bool} (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbE ε (dpbP ε W) = (1 / 4 : ℝ) • (W + Wᴴ - Jm ε * W * Jm ε - (Jm ε * W * Jm ε)ᴴ) := by
  ext a b
  simp only [dpbE, dpbP, LinearMap.coe_mk, AddHom.coe_mk, pmat, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, dpb_JWJ]
  by_cases hε : ε a = ε b
  · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => h.2 hε
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => h.2 hε.symm
    rw [dif_neg h1, dif_neg h2, if_pos hε, if_pos hε.symm]
    simp
  · rw [if_neg hε, if_neg (Ne.symm hε)]
    rcases lt_trichotomy a b with h | h | h
    · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => absurd h'.1 (not_lt.mpr h.le)
      rw [dif_neg h1, dif_pos (And.intro h (Ne.symm hε))]
      simp only [Complex.real_smul]
      push_cast
      simp only [star_add, star_mul', star_star, star_div₀, star_one, star_ofNat, star_neg]
      ring
    · exact absurd (h ▸ rfl) hε
    · rw [dif_pos (And.intro h hε)]
      simp only [star_neg, Complex.real_smul]
      push_cast
      ring

theorem dpb_JYJ {ε : Fin n → Bool} (y : PCoord ε → ℂ) : Jm ε * pmat y * Jm ε = -pmat y := by
  ext a b
  rw [dpb_JWJ]
  split_ifs with h
  · have : pmat y a b = 0 := by simp [pmat, h]
    rw [Matrix.neg_apply, this, neg_zero]
  · rw [Matrix.neg_apply]

theorem dpb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.sinh_neg, neg_div_neg_eq]

theorem dpb_shc_fac : (fun u : ℝ => u * ((shc u - 1) / u)) = fun u => shc u - 1 := by
  funext u
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg h]
    field_simp

theorem dpb_theta_ad {J Y : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hY : J * Y * J = -Y)
    (W : Matrix (Fin n) (Fin n) ℂ) : J * (Y * W - W * Y) * J = -(Y * (J * W * J) - (J * W * J) * Y) := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (J * A * J) * (J * B * J) = J * (A * B) * J := by
    intro A B
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← key Y W, ← key W Y, hY]
  simp only [neg_mul, mul_neg]
  abel

theorem dpb_det {ε : Fin n → Bool} {U : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hY : Jm ε * (U * dpbD x * Uᴴ) * Jm ε = -(U * dpbD x * Uᴴ)) :
    LinearMap.det (dpbL U x shc) = LinearMap.det (dpbP ε ∘ₗ dpbL U x shc ∘ₗ dpbE ε) ^ 4 := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    change star (if ε a then (1 : ℂ) else -1) = (if ε a then 1 else -1)
    split_ifs <;> simp
  have hJJv : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let θ : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Jm ε * W * Jm ε
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c W => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let α : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Wᴴ
      map_add' := fun W W' => Matrix.conjTranspose_add W W'
      map_smul' := fun c W => by simp [Matrix.conjTranspose_smul] }
  let ι : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Complex.I • W
      map_add' := fun W W' => smul_add _ _ _
      map_smul' := fun c W => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  let N : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => (U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c W => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  let C : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) := dpbL U x (fun u => (shc u - 1) / u)
  have hsub : dpbH U x (fun u => u * ((shc u - 1) / u)) = dpbH U x (fun u => shc u - 1) := by
    rw [dpb_shc_fac]
  refine dpb_abs (dpbL U x shc) θ α ι N C (dpbE ε) (dpbP ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    show Jm ε * (Jm ε * v * Jm ε) * Jm ε = v
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJv]
  · intro v
    show (vᴴ)ᴴ = v
    exact Matrix.conjTranspose_conjTranspose v
  · intro v
    show Jm ε * vᴴ * Jm ε = (Jm ε * v * Jm ε)ᴴ
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]
  · intro v
    show Jm ε * dpbH U x shc v * Jm ε = dpbH U x shc (Jm ε * v * Jm ε)
    exact dpbH_theta hU hU' hJJ hJh hY shc dpb_shc_neg v
  · intro v
    show (dpbH U x shc v)ᴴ = dpbH U x shc vᴴ
    exact dpbH_conjTranspose U x shc dpb_shc_neg v
  · intro v
    show (U * dpbD x * Uᴴ) * dpbH U x (fun u => (shc u - 1) / u) v -
      dpbH U x (fun u => (shc u - 1) / u) v * (U * dpbD x * Uᴴ) = dpbH U x shc v - v
    rw [dpbH_ad_left x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show dpbH U x (fun u => (shc u - 1) / u) ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) =
      dpbH U x shc v - v
    rw [dpbH_ad_right x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show Jm ε * ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) * Jm ε =
      -((U * dpbD x * Uᴴ) * (Jm ε * v * Jm ε) - (Jm ε * v * Jm ε) * (U * dpbD x * Uᴴ))
    exact dpb_theta_ad hJJ hY v
  · intro v
    show Complex.I • (Complex.I • v) = -v
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  · intro v
    show Complex.I • dpbH U x shc v = dpbH U x shc (Complex.I • v)
    exact (dpbH_smul U x shc Complex.I v).symm
  · intro v
    show Jm ε * (Complex.I • v) * Jm ε = Complex.I • (Jm ε * v * Jm ε)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  · intro v
    show (Complex.I • v)ᴴ = -(Complex.I • vᴴ)
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · intro v
    exact dpbE_P v
  · intro w
    exact dpbP_E w

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma pmat_entry_cases {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a b : Fin n) :
    pmat z a b = 0 ∨ ε a ≠ ε b := by
  unfold pmat
  split_ifs with h h'
  · exact Or.inr h.2
  · exact Or.inr (Ne.symm h'.2)
  · exact Or.inl rfl

lemma jsgn_ne {x y : Bool} (h : x ≠ y) :
    ((if y then 1 else -1 : ℂ)) = -(if x then 1 else -1) := by
  cases x <;> cases y <;> simp at h ⊢

theorem pmat_inP {ε : Fin n → Bool} (z : PCoord ε → ℂ) : inP ε (pmat z) := by
  have h2 : pmat z * Jm ε = -(Jm ε * pmat z) := by
    ext a b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
    rcases pmat_entry_cases z a b with h | h
    · rw [h]
      simp
    · rw [jsgn_ne h]
      ring
  refine ⟨?_, h2⟩
  unfold inG
  rw [(pmat_isHermitian z).eq, h2]
  simp

theorem pmat_coords {ε : Fin n → Bool} (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) :
    pmat (fun ab : PCoord ε => X ab.1.1 ab.1.2) = X := by
  obtain ⟨hG, hJ⟩ := hX
  unfold inG at hG
  have hent : ∀ a b, X a b * (if ε b then 1 else -1) = -((if ε a then 1 else -1) * X a b) := by
    intro a b
    have h := congrFun (congrFun hJ a) b
    simpa [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] using h
  have hzero : ∀ a b, ε a = ε b → X a b = 0 := by
    intro a b hab
    have h := hent a b
    rw [hab] at h
    cases hb : ε b <;> simp [hb] at h <;>
      first
        | exact h
        | linear_combination h / 2
        | linear_combination (-1 / 2 : ℂ) * h
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    cases ε a <;> simp
  have hH : Xᴴ = X := by
    have h1 : Xᴴ * Jm ε = X * Jm ε := by
      rw [hJ]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = X * Jm ε * Jm ε := by rw [h1]
      _ = X := by rw [mul_assoc, hJJ, mul_one]
  ext a b
  unfold pmat
  split_ifs with h h'
  · rfl
  · have h3 := congrFun (congrFun hH a) b
    rw [Matrix.conjTranspose_apply] at h3
    exact h3
  · apply (hzero a b ?_).symm
    rcases lt_trichotomy a b with hab | hab | hab
    · by_contra hne
      exact h' ⟨hab, Ne.symm hne⟩
    · rw [hab]
    · by_contra hne
      exact h ⟨hab, hne⟩

def pmatHalfSq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (ab : Fin n × Fin n) : ℝ :=
  if h : ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2 then ‖z ⟨ab, h⟩‖ ^ 2 else 0

lemma norm_pmat_sq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a b : Fin n) :
    ‖pmat z a b‖ ^ 2 = pmatHalfSq z (a, b) + pmatHalfSq z (b, a) := by
  unfold pmat pmatHalfSq
  dsimp only
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => lt_asymm h1.1 h.1
    simp only [dif_pos h1, dif_neg h2, add_zero]
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [dif_neg h1, dif_pos h2, norm_star, zero_add]
    · simp only [dif_neg h1, dif_neg h2, norm_zero, add_zero]
      norm_num

lemma sum_pmatHalfSq {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ ab : Fin n × Fin n, pmatHalfSq z ab = ∑ ab : PCoord ε, ‖z ab‖ ^ 2 := by
  classical
  have e1 : ∑ ab : Fin n × Fin n, pmatHalfSq z ab =
      ∑ ab ∈ univ.filter (fun ab : Fin n × Fin n => ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2), pmatHalfSq z ab := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ab _ => ?_
    split_ifs with h
    · rfl
    · unfold pmatHalfSq
      rw [dif_neg h]
  rw [e1, Finset.sum_subtype (p := fun ab : Fin n × Fin n => ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2) _
    (fun ab => by simp) (pmatHalfSq z)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  unfold pmatHalfSq
  rw [dif_pos ab.2]

theorem hs_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : hs (pmat z) = 2 * ∑ ab, ‖z ab‖ ^ 2 := by
  unfold S7.hs
  have e : ∀ i j, ‖pmat z i j‖ ^ 2 = pmatHalfSq z (i, j) + pmatHalfSq z (j, i) := norm_pmat_sq z
  simp only [e, Finset.sum_add_distrib]
  have hprod : ∑ i, ∑ j, pmatHalfSq z (i, j) = ∑ ab : Fin n × Fin n, pmatHalfSq z ab :=
    (Fintype.sum_prod_type' (fun i j => pmatHalfSq z (i, j))).symm
  have hswap : ∑ i, ∑ j, pmatHalfSq z (j, i) = ∑ i, ∑ j, pmatHalfSq z (i, j) := Finset.sum_comm
  rw [hswap, hprod, sum_pmatHalfSq]
  ring

lemma pmat_diag_zero {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a : Fin n) : pmat z a a = 0 := by
  simp [pmat]

theorem sum_pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) : ∑ a, pev z a = 0 := by
  have h := (pmat_isHermitian z).trace_eq_sum_eigenvalues
  have htr : (pmat z).trace = 0 := by simp [Matrix.trace, pmat_diag_zero]
  rw [htr] at h
  unfold pev
  have h2 : (((∑ i, (pmat_isHermitian z).eigenvalues i : ℝ)) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]
    exact h.symm
  have h3 := Complex.ofReal_eq_zero.mp h2
  convert h3 using 2

theorem card_PCoord (ε : Fin n → Bool) : Fintype.card (PCoord ε) = pOf ε * qOf ε := by
  classical
  rw [Fintype.card_subtype, pOf, qOf, ← Finset.card_product]
  refine Finset.card_nbij' (fun ab => if ε ab.1 then ab else (ab.2, ab.1))
    (fun xy => (max xy.1 xy.2, min xy.1 xy.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h
    obtain ⟨hba, hne⟩ := h
    cases ha : ε a <;> cases hb : ε b <;> simp_all
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_setOf_eq] at h
    obtain ⟨hx, hy⟩ := h
    have hxy : x ≠ y := by
      intro e
      rw [e, hy] at hx
      exact Bool.false_ne_true hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [max_eq_right h.le, min_eq_left h.le]
      exact ⟨h, by rw [hx, hy]; decide⟩
    · rw [max_eq_left h.le, min_eq_right h.le]
      exact ⟨h, by rw [hx, hy]; decide⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h
    obtain ⟨hba, hne⟩ := h
    cases ha : ε a
    · simp only [ha, Bool.false_eq_true, if_false]
      rw [max_eq_right hba.le, min_eq_left hba.le]
    · simp only [ha, if_true]
      rw [max_eq_left hba.le, min_eq_right hba.le]
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_setOf_eq] at h
    obtain ⟨hx, hy⟩ := h
    have hxy : x ≠ y := by
      intro e
      rw [e, hy] at hx
      exact Bool.false_ne_true hx
    dsimp only
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [max_eq_right h.le, min_eq_left h.le]
      simp [hy]
    · rw [max_eq_left h.le, min_eq_right h.le]
      simp [hx]

end ReciprocityTheory.ChartRestriction.DS
end
end
