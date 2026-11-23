module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded
import Aesop.Frontend.Tactic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

namespace CoordinateExpansion

theorem exp_localHomeo (n : ℕ) :
    ∃ e : OpenPartialHomeomorph (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ),
      (0 : Matrix (Fin n) (Fin n) ℂ) ∈ e.source ∧ ∀ Z ∈ e.source, e Z = NormedSpace.exp Z := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
    exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix (Fin n) (Fin n) ℂ)
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, fun Z _ => rfl⟩

variable {n : ℕ}

def coord (Z : Matrix (Fin n) (Fin n) ℂ) (p : Fin n × Fin n) : ℝ :=
  if p.1 = p.2 then (Z p.1 p.1).im else if p.1 < p.2 then (Z p.1 p.2).re else (Z p.2 p.1).im

theorem continuous_coord (p : Fin n × Fin n) : Continuous fun Z : Matrix (Fin n) (Fin n) ℂ => coord Z p := by
  unfold coord
  split_ifs
  · exact Complex.continuous_im.comp (continuous_id.matrix_elem _ _)
  · exact Complex.continuous_re.comp (continuous_id.matrix_elem _ _)
  · exact Complex.continuous_im.comp (continuous_id.matrix_elem _ _)

theorem entry_of_inG {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) (a b : Fin n) :
    Z a b = -((sg ε (a, b) : ℝ) : ℂ) * star (Z b a) := by
  have h := congrFun (congrFun hZ a) b
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Jm, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  simp only [sg]
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

theorem sg_swap (ε : Fin n → Bool) (a b : Fin n) : sg ε (b, a) = sg ε (a, b) := by
  simp only [sg]
  by_cases h : ε a = ε b
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

theorem gen_apply_zero (ε : Fin n → Bool) (p : Fin n × Fin n) (i j : Fin n) (h1 : p ≠ (i, j)) (h2 : p ≠ (j, i)) :
    gen ε p i j = 0 := by
  obtain ⟨p1, p2⟩ := p
  simp only [ne_eq, Prod.mk.injEq] at h1 h2
  unfold gen
  split_ifs <;> simp [Matrix.single_apply] <;> aesop

theorem eq_sum_gen {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    Z = ∑ p, ((coord Z p : ℝ) : ℂ) • gen ε p := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne])
      (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]
    simp [coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply]
  · rw [Fintype.sum_eq_single (i, i) (fun q hq => by rw [gen_apply_zero ε q i i hq hq, mul_zero])]
    have he := entry_of_inG hZ i i
    simp only [sg, if_true] at he
    have hre : (Z i i).re = 0 := by
      have h2 := congrArg Complex.re he
      simp at h2
      linarith
    simp [coord, gen, Matrix.single_apply]
    try (apply Complex.ext <;> simp [hre])
  · rw [Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne'])
      (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]
    rw [entry_of_inG hZ i j]
    simp [coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply, sg_swap]
    try (apply Complex.ext <;> simp <;> ring)

theorem inG_of_log {ε : Fin n → Bool} (e : OpenPartialHomeomorph (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ))
    (hee : ∀ Z ∈ e.source, e Z = NormedSpace.exp Z) {Z g : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ e.source)
    (hτZ : -(Jm ε * Zᴴ * Jm ε) ∈ e.source) (hg : inUJ ε g) (hZg : NormedSpace.exp Z = g) : inG ε Z := by

  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse hJJ)
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    split_ifs with ha <;> simp [ha]
  have hg' : gᴴ * Jm ε * g = Jm ε := hg

  have hgl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJJ]
  have hgi : g⁻¹ = Jm ε * gᴴ * Jm ε := Matrix.inv_eq_left_inv hgl
  have key : NormedSpace.exp (-(Jm ε * Zᴴ * Jm ε)) = g := by
    have h1 : -(Jm ε * Zᴴ * Jm ε) = Jm ε * (-Z)ᴴ * (Jm ε)⁻¹ := by
      rw [hJi, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [h1, Matrix.exp_conj _ _ hJu, Matrix.exp_conjTranspose, Matrix.exp_neg, hZg, hgi, hJi,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh]
    simp only [← Matrix.mul_assoc]
    rw [hJJ, Matrix.one_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hτ : -(Jm ε * Zᴴ * Jm ε) = Z := e.injOn hτZ hZ (by rw [hee _ hτZ, hee _ hZ, key, hZg])
  show Zᴴ * Jm ε + Jm ε * Z = 0
  have hJZ : Jm ε * Z = -(Zᴴ * Jm ε) := by
    calc Jm ε * Z = Jm ε * (-(Jm ε * Zᴴ * Jm ε)) := by rw [hτ]
      _ = -(Zᴴ * Jm ε) := by
        rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [hJZ, add_neg_cancel]

end CoordinateExpansion

theorem c6 : SmallMotionNeighbourhood := by
  intro n ε H _ _ _ σ D hD W C' hC' hdense
  obtain ⟨e, he0, hee⟩ := CoordinateExpansion.exp_localHomeo n
  set M := max C' 0 with hM
  let τ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun Z => -(Jm ε * Zᴴ * Jm ε)
  have hτ : Continuous τ :=
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).neg
  let V : Set (Matrix (Fin n) (Fin n) ℂ) :=
    e.source ∩ τ ⁻¹' e.source ∩ {Z | (∑ p, |CoordinateExpansion.coord Z p|) * M < 1 / 2}
  have hVo : IsOpen V := by
    refine (e.open_source.inter (e.open_source.preimage hτ)).inter (isOpen_lt ?_ continuous_const)
    exact (continuous_finsetSum _ fun p _ => (CoordinateExpansion.continuous_coord p).abs).mul continuous_const
  have hV0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ V := by
    refine ⟨⟨he0, ?_⟩, ?_⟩
    · simpa [τ] using he0
    · simp [CoordinateExpansion.coord]
  have himg : IsOpen (e '' V) := e.isOpen_image_of_subset_source hVo (fun Z h => h.1.1)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ e '' V := ⟨0, hV0, by rw [hee 0 he0, NormedSpace.exp_zero]⟩
  refine ⟨(fun g : UJ ε => umat g) ⁻¹' (e '' V), ?_, ?_⟩
  · exact continuous_umat.continuousAt.preimage_mem_nhds (himg.mem_nhds (by exact h1))
  · rintro g ⟨Z, hZV, hZg⟩ v hv
    have hZg' : NormedSpace.exp Z = umat g := by rw [← hee Z hZV.1.1]; exact hZg
    have hG : inG ε Z := CoordinateExpansion.inG_of_log e hee hZV.1.1 hZV.1.2 (umat_mem g) hZg'
    have key : ((D ⊓ W : Submodule ℂ H) : Set H) ⊆ {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2} := by
      intro u hu
      have huD : u ∈ D := hu.1
      have huW : u ∈ W := hu.2
      show ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2
      rw [← hZg']
      calc ‖σ (NormedSpace.exp Z) u - u‖ ≤ ‖dS σ Z u‖ := hD.mv Z hG u huD
        _ = ‖∑ p, ((CoordinateExpansion.coord Z p : ℝ) : ℂ) • dS σ (gen ε p) u‖ := by
          rw [← hD.lin _ u huD, ← CoordinateExpansion.eq_sum_gen hG]
        _ ≤ ∑ p, |CoordinateExpansion.coord Z p| * (M * ‖u‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ((hC' p u huD huW).trans ?_) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = ((∑ p, |CoordinateExpansion.coord Z p|) * M) * ‖u‖ := by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by ring
        _ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right hZV.2.le (norm_nonneg _)
        _ = ‖u‖ / 2 := by ring
    have hcl : IsClosed {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2} :=
      isClosed_le (((σ (umat g)).continuous.sub continuous_id).norm) (continuous_norm.div_const _)
    exact closure_minimal key hcl (hdense v hv)

end Formalism.L2.SG.Pf.admitted
end
end

section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CoefficientIntegrals

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem re_coef_ge {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {g : UJ ε} {v : H} (hv : ‖v‖ = 1)
    (h : ‖σ (umat g) v - v‖ ≤ ‖v‖ / 2) : (1 / 2 : ℝ) ≤ (coefOn σ v v g).re := by
  have h1 : coefOn σ v v g = ⟪v, v⟫_ℂ + ⟪v, σ (umat g) v - v⟫_ℂ := by
    simp [coefOn]
  have h2 : ‖⟪v, σ (umat g) v - v⟫_ℂ‖ ≤ 1 / 2 := by
    calc _ ≤ ‖v‖ * ‖σ (umat g) v - v‖ := norm_inner_le_norm _ _
      _ ≤ 1 / 2 := by rw [hv] at h ⊢; linarith
  have h4 := (abs_le.1 ((Complex.abs_re_le_norm _).trans h2)).1
  have h5 : (⟪v, v⟫_ℂ).re = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hv] at this
    simpa using this
  rw [h1, Complex.add_re, h5]
  linarith

def sumCoef {ι : Type} [Fintype ι] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : ι → H) (g : UJ ε) : ℂ :=
  ∑ i, coefOn σ (v i) (v i) g

theorem re_sumCoef_ge {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H}
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) {g : UJ ε}
    (hg : ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2) :
    (Fintype.card ι : ℝ) / 2 ≤ (sumCoef σ v g).re := by
  unfold sumCoef
  rw [Complex.re_sum]
  have hi : ∀ i, (1 / 2 : ℝ) ≤ (coefOn σ (v i) (v i) g).re := fun i =>
    re_coef_ge (hv.1 i) (hg _ (hW i))
  calc (Fintype.card ι : ℝ) / 2 = ∑ _i : ι, (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

theorem integral_sumCoef {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {d : ℝ} (hd : IsFdeg (muG ε) σ d) {v : ι → H} (hv : Orthonormal ℂ v) :
    Integrable (fun g => sumCoef σ v g * star (sumCoef σ v g)) (muG ε) ∧
      ∫ g, sumCoef σ v g * star (sumCoef σ v g) ∂(muG ε) = (Fintype.card ι : ℂ) / (d : ℂ) := by
  have hexp : (fun g : UJ ε => sumCoef σ v g * star (sumCoef σ v g)) = fun g =>
      ∑ i, ∑ j, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) := by
    funext g
    unfold sumCoef
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hint : ∀ i j, Integrable
      (fun g => coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g)) (muG ε) :=
    fun i j => (hd.2 _ _ _ _).1
  have hij : ∀ i j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) =
      if i = j then 1 / (d : ℂ) else 0 := by
    intro i j
    rw [(hd.2 _ _ _ _).2, orthonormal_iff_ite.mp hv j i, orthonormal_iff_ite.mp hv i j]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine ⟨?_, ?_⟩
  · rw [hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  · rw [hexp, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    calc _ = ∑ i, ∑ j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact integral_finsetSum _ fun j _ => hint i j
      _ = _ := by
          simp only [hij, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring

theorem card_le {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (muG ε) σ d) {W : Submodule ℂ H} {K : Set (UJ ε)} (hKm : MeasurableSet K)
    (hKf : muG ε K ≠ ⊤) (hKpos : 0 < (muG ε).real K)
    (hK : ∀ g ∈ K, ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2)
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) :
    (Fintype.card ι : ℝ) ≤ 4 / (d * (muG ε).real K) := by
  classical
  set m := (Fintype.card ι : ℝ) with hmdef
  obtain ⟨hint, hval⟩ := integral_sumCoef hd hv
  let f : UJ ε → ℝ := fun g => (sumCoef σ v g * star (sumCoef σ v g)).re
  have hfint : Integrable f (muG ε) := hint.re
  have hfn : ∀ g, f g = Complex.normSq (sumCoef σ v g) := fun g => by
    simp [f, Complex.mul_conj]
  have hf0 : ∀ g, 0 ≤ f g := fun g => by rw [hfn]; exact Complex.normSq_nonneg _
  have hm0 : 0 ≤ m := by positivity
  have hK' : ∀ g ∈ K, (m / 2) ^ 2 ≤ f g := by
    intro g hg
    have h1 := re_sumCoef_ge hv hW (hK g hg)
    rw [hfn, Complex.normSq_apply]
    nlinarith [sq_nonneg (sumCoef σ v g).im]
  have hset : (m / 2) ^ 2 * (muG ε).real K ≤ ∫ g in K, f g ∂(muG ε) :=
    by
      have := setIntegral_ge_of_const_le hKm hKf hK' hfint.integrableOn
      rwa [smul_eq_mul, mul_comm] at this
  have hle : ∫ g in K, f g ∂(muG ε) ≤ ∫ g, f g ∂(muG ε) :=
    setIntegral_le_integral hfint (Filter.Eventually.of_forall hf0)
  have htot : ∫ g, f g ∂(muG ε) = m / d := by
    show ∫ g, (sumCoef σ v g * star (sumCoef σ v g)).re ∂(muG ε) = m / d
    have hc : ((Fintype.card ι : ℂ) / (d : ℂ)) = ((m / d : ℝ) : ℂ) := by
      rw [hmdef]
      push_cast
      ring
    have hr := integral_re hint
    simp only [RCLike.re_to_complex] at hr
    rw [hr, hval, hc, Complex.ofReal_re]
  have hd0 := hd.1
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · rw [← h0]
    exact div_nonneg (by norm_num) (mul_pos hd0 hKpos).le
  · rw [le_div_iff₀ (mul_pos hd0 hKpos)]
    have hA : (m / 2) ^ 2 * (muG ε).real K ≤ m / d := (hset.trans hle).trans_eq htot
    have hB : (m / 2) ^ 2 * (muG ε).real K * d ≤ m := by
      have := mul_le_mul_of_nonneg_right hA hd0.le
      rwa [div_mul_cancel₀ _ hd0.ne'] at this
    nlinarith [hB, hpos, mul_pos hd0 hKpos]

end CoefficientIntegrals

open CoefficientIntegrals in
theorem c7 : FormalDegreeFiniteDim := by
  intro n ε H _ _ _ σ _ d hd W U hU hUW
  classical
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKf : muG ε K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < (muG ε).real K :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne' hKf
  have hbound : ∀ (m : ℕ) (v : Fin m → H), Orthonormal ℂ v → (∀ i, v i ∈ W) →
      (m : ℝ) ≤ 4 / (d * (muG ε).real K) := by
    intro m v hv hvW
    simpa using card_le hd hKm hKf hKpos (fun g hg => hUW g (hKU hg)) hv hvW
  by_contra hfin
  obtain ⟨m, hm⟩ := exists_nat_gt (4 / (d * (muG ε).real K))
  let bW := Module.Basis.ofVectorSpace ℂ W
  have hI : (Module.Basis.ofVectorSpaceIndex ℂ W).Infinite := by
    intro hfinI
    haveI : Finite (Module.Basis.ofVectorSpaceIndex ℂ W) := hfinI.to_subtype
    exact hfin (Module.Finite.of_basis bW)
  obtain ⟨t, htsub, htcard⟩ := hI.exists_subset_card_eq m
  let u : t → W := fun x => bW ⟨x.1, htsub x.2⟩
  have hu : LinearIndependent ℂ u :=
    bW.linearIndependent.comp _ (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  let F : Submodule ℂ W := Submodule.span ℂ (Set.range u)
  haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hF : Module.finrank ℂ F = m := by
    rw [finrank_span_eq_card hu]
    simp [htcard]
  let ob := stdOrthonormalBasis ℂ F
  let v : Fin (Module.finrank ℂ F) → H := fun i => ((ob i : F) : W)
  have hv : Orthonormal ℂ v :=
    (ob.orthonormal.comp_linearIsometry F.subtypeₗᵢ).comp_linearIsometry W.subtypeₗᵢ
  have h := hbound _ v hv (fun i => ((ob i : F) : W).2)
  rw [hF] at h
  linarith

end Formalism.L2.SG.Pf.admitted
end
end

section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ExponentialDecomposition

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kavg_fix_range {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) (Θ : S →ₗ[ℂ] H)
    (hΘ : ∀ (a : KG ε) (v w : S), (w : H) = σ (toMK a) v → Θ w = σ (toMK a) (Θ v)) (s : S) :
    kavg hσ he (Θ s) = Θ s := by
  have hs : kavg hσ he (s : H) = s := hfix s s.2
  have hval : ∀ x : H, kavg hσ he x = ∫ k, e k • σ (toMK k) x ∂muK ε := fun x => by
    unfold Formalism.MainNotions.BridgeCPX.kavg
    rfl
  have hkS : ∀ k : KG ε, σ (toMK k) s ∈ S := fun k => hst _ k.2 _ s.2
  let F : KG ε → S := fun k => e k • ⟨σ (toMK k) s, hkS k⟩
  have hΘF : ∀ k, Θ (F k) = e k • σ (toMK k) (Θ s) := fun k => by
    simp only [F, map_smul]
    rw [hΘ k s ⟨σ (toMK k) s, hkS k⟩ rfl]
  have hsub : ((∫ k, F k ∂muK ε : S) : H) = ∫ k, (F k : H) ∂muK ε :=
    (S.subtypeₗᵢ.integral_comp_comm F).symm
  have hint : (∫ k, F k ∂muK ε) = s := by
    apply Subtype.ext
    rw [hsub, ← hs, hval]
    rfl
  rw [hval, integral_congr_ae (Filter.Eventually.of_forall fun k => (hΘF k).symm)]
  by_cases hFi : Integrable F (muK ε)
  · have h := (LinearMap.toContinuousLinearMap Θ).integral_comp_comm hFi
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    rw [h, hint]
  · rw [integral_undef hFi] at hint
    subst hint
    have h0 : ∀ k, F k = 0 := fun k => by
      ext
      simp [F]
    simp only [h0, map_zero, integral_zero]

theorem kavg_fix_isoK {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) {v : H} (hv : v ∈ isoK ε σ S) :
    kavg hσ he v = v := by
  have hle : isoK ε σ S ≤ LinearMap.ker
      ((((kavg hσ he : H →L[ℂ] H) - ContinuousLinearMap.id ℂ H : H →L[ℂ] H)) : H →ₗ[ℂ] H) := by
    refine sSup_le ?_
    rintro T ⟨Θ, hΘ, rfl⟩
    rintro x ⟨s, rfl⟩
    simp [LinearMap.mem_ker, sub_eq_zero, kavg_fix_range hσ hst he hfix Θ hΘ s]
  have h := hle hv
  simpa [LinearMap.mem_ker, sub_eq_zero] using h

end ExponentialDecomposition

theorem c0 : SmoothVectorsDense := by
  intro n ε H _ _ _ σ hσ hirr w hw S hfd hst v hv
  obtain ⟨e, he, hfix, hrange⟩ := compactProj (KG ε) (muK ε) H (fun k : KG ε => σ (toMK k)) hσ.1.1
    (fun a b => hσ.1.2 _ (umat_mem (a : UJ ε)) _ (umat_mem (b : UJ ε)))
    (fun a v => hσ.2.1 _ (umat_mem (a : UJ ε)) v)
    (fun v => (cont_orbit hσ v).comp continuous_subtype_val) S hfd (fun a v hv => hst _ a.2 v hv)
  have hfix' : ∀ x ∈ S, kavg hσ he x = x := fun x hx => by
    rw [kavg_apply]
    exact hfix x hx
  have hE : kavg hσ he v = v := ExponentialDecomposition.kavg_fix_isoK hσ hst he hfix' hv
  have hvc : v ∈ closure (Vsub ε hσ w : Set H) := by
    have h := Vsub_dense hσ hirr hw
    have h2 : v ∈ (Vsub ε hσ w).topologicalClosure := by
      rw [h]
      trivial
    exact h2
  have h3 : kavg hσ he v ∈ closure ((Vsub ε hσ w ⊓ isoK ε σ S : Submodule ℂ H) : Set H) := by
    refine map_mem_closure (kavg hσ he).continuous hvc ?_
    rintro _ ⟨Φ, hΦ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_inf]
    refine ⟨⟨kconv ε e Φ, test_kconv he hΦ, kavg_vec hσ w he hΦ⟩, ?_⟩
    rw [kavg_apply]
    exact hrange _
  rwa [hE] at h3

end Formalism.L2.SG.Pf.admitted
end
end
