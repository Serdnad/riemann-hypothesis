module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inner_map_of_isometry {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (f : E →L[ℂ] F) (hf : ∀ x, ‖f x‖ = ‖x‖) (x y : E) :
    ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let fi : E →ₗᵢ[ℂ] F := ⟨f.toLinearMap, hf⟩
  exact fi.inner_map_map x y

theorem toMK_mem_UJset' {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ UJset ε := by
  show inUJ ε (toMK k)
  first
  | exact k.1.2
  | exact k.val.property
  | exact (k : UJ ε).2

theorem toMK_inv_mul {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ * toMK k = 1 := by
  have h : toMK k⁻¹ * toMK k = toMK (k⁻¹ * k) := rfl
  rw [h, inv_mul_cancel]
  rfl

theorem op_op_inv {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (v : T.V) :
    T.op k (T.op k⁻¹ v) = v := by
  have h : (T.τ k) * (T.τ k⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 := congrArg (fun u : unitary (T.V →L[ℂ] T.V) => (u : T.V →L[ℂ] T.V) v) h
  first
  | (rw [Submonoid.coe_mul, ContinuousLinearMap.mul_apply, OneMemClass.coe_one,
      ContinuousLinearMap.one_apply] at h2; exact h2)
  | exact h2
  | (simp only [Submonoid.coe_mul, ContinuousLinearMap.mul_apply, OneMemClass.coe_one,
      ContinuousLinearMap.one_apply] at h2; exact h2)

theorem sum_inner_basis_sq_eq_adjoint {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {T : KType ε (lowK ε lam)} {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ T.V) (k : KG ε) (y : H) :
    ∑ l, ‖⟪j (b l), σ (toMK k) y⟫_ℂ‖ ^ 2 =
      ‖(ContinuousLinearMap.adjoint j) y‖ ^ 2 := by
  have hσ1 : σ (toMK k⁻¹) (σ (toMK k) y) = y := by
    have h := hF.urep.1.2 _ (toMK_mem_UJset' k⁻¹) _ (toMK_mem_UJset' k)
    rw [← ContinuousLinearMap.comp_apply, ← h, toMK_inv_mul, hF.urep.1.1]
    rfl
  have key : ∀ l, ⟪j (b l), σ (toMK k) y⟫_ℂ = ⟪b l, T.op k (ContinuousLinearMap.adjoint j y)⟫_ℂ := by
    intro l
    rw [← inner_map_of_isometry (σ (toMK k⁻¹)) (hF.urep.2.1 _ (toMK_mem_UJset' k⁻¹)), hσ1, hF.kequiv,
      ← ContinuousLinearMap.adjoint_inner_right, ← Unitary.inner_map_map (T.τ k)]
    rw [show ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) (T.op k⁻¹ (b l)) = b l from
      op_op_inv T k (b l)]
  simp_rw [key]
  rw [b.sum_sq_norm_inner_right, Unitary.norm_map]

theorem haar_univ_eq_one (ε : Fin n → Bool) : dk ε Set.univ = 1 :=
  (CompactHaarProbability.dk_isProb ε).measure_univ

theorem hsOp_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) : 0 ≤ hsOp A := by
  unfold hsOp
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem lemma6a {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2 / d) =
      ENNReal.ofReal (cPQ ε) * ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
  classical
  let b := stdOrthonormalBasis ℂ T.V
  let c : Fin (Module.finrank ℂ T.V) → Fin (Module.finrank ℂ T.V) → Matrix (Fin n) (Fin n) ℂ → ℝ := fun i l x => ‖⟪j (b l), σ x (j (b i))⟫_ℂ‖ ^ 2
  let f : (Fin n → Fin n → ℂ) → ENNReal := fun x => ENNReal.ofReal (∑ i, ∑ l, c i l x)
  let S : Set (Fin n → Fin n → ℂ) := UJset ε
  let F : (Fin n → Fin n → ℂ) → ENNReal := S.piecewise f 0
  have hFm : Measurable F := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn ?_
    · refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun l _ => ?_))
      have hc : ContinuousOn (fun x : Fin n → Fin n → ℂ => σ x (j (b i))) S := hF.urep.2.2 (j (b i))
      exact ((continuousOn_const.inner hc).norm.pow 2)
    · have hS : IsClosed S := isClosed_inUJ ε
      exact hS.measurableSet
  have hbb : ∀ i, ⟪j (b i), j (b i)⟫_ℂ = 1 := by
    intro i
    rw [inner_map_of_isometry j hF.iso, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hc_int : ∀ i l, Integrable (fun g : Formalism.REAL.UJ ε => c i l (Formalism.MainNotions.S.umat g)) (muCD ε) ∧
      ∫ g, c i l (Formalism.MainNotions.S.umat g) ∂(muCD ε) = 1 / d := by
    intro i l
    obtain ⟨hI, hE⟩ := (hd.2 (j (b i)) (j (b l)) (j (b i)) (j (b l)))
    have hre : ∀ g : Formalism.REAL.UJ ε, RCLike.re (Formalism.MainNotions.S.coefOn (ε := ε) σ (j (b i)) (j (b l)) g *
        star (Formalism.MainNotions.S.coefOn (ε := ε) σ (j (b i)) (j (b l)) g)) = c i l (Formalism.MainNotions.S.umat g) := by
      intro g
      simp only [c, Formalism.MainNotions.S.coefOn]
      rw [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    refine ⟨hI.re.congr (Filter.Eventually.of_forall hre), ?_⟩
    rw [← integral_congr_ae (Filter.Eventually.of_forall hre), integral_re hI, hE, hbb, hbb, one_mul]
    simp
  have hL : ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2 / d) = ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε) := by
    have hFg : ∀ g : Formalism.REAL.UJ ε,
        F (Formalism.MainNotions.S.umat g) = ENNReal.ofReal (∑ i, ∑ l, c i l (Formalism.MainNotions.S.umat g)) := by
      intro g
      have hm : (Formalism.MainNotions.S.umat g : Fin n → Fin n → ℂ) ∈ S := by
        have h : Formalism.REAL.inUJ ε (Formalism.MainNotions.S.umat g) := g.2
        unfold Formalism.REAL.inUJ Formalism.REAL.Jm at h
        show inUJ ε _
        unfold inUJ Jm
        exact h
      exact Set.piecewise_eq_of_mem S f 0 hm
    simp_rw [hFg]
    have hsum : Integrable (fun g : Formalism.REAL.UJ ε => ∑ i, ∑ l, c i l (Formalism.MainNotions.S.umat g)) (muCD ε) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => (hc_int i l).1))
    rw [← ofReal_integral_eq_lintegral_ofReal hsum
      (Filter.Eventually.of_forall (fun g => sum_nonneg (fun i _ => sum_nonneg (fun l _ => by positivity))))]
    congr 1
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => (hc_int i l).1))]
    have hi : ∀ i, ∫ g, ∑ l, c i l (Formalism.MainNotions.S.umat g) ∂(muCD ε) = (Module.finrank ℂ T.V : ℝ) * (1 / d) := by
      intro i
      rw [integral_finsetSum _ (fun l _ => (hc_int i l).1)]
      simp only [(hc_int _ _).2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [hi, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hval : ∀ (k : KG ε) (z : PCoord ε → ℂ), ∑ i, ∑ l, c i l (polarM (k, z)) = hsOp (fF ε lam T (pmat z)) := by
    intro k z
    have hσ : σ (polarM (k, z)) = (σ (toMK k)).comp (σ (NormedSpace.exp (pmat z))) :=
      hF.urep.1.2 _ (toMK_mem_UJset' k) _ (exp_pmat_inUJ z)
    unfold hsOp
    refine sum_congr rfl (fun i _ => ?_)
    simp only [c, hσ, ContinuousLinearMap.comp_apply]
    refine (sum_inner_basis_sq_eq_adjoint hF b k _).trans ?_
    rw [← hF.formF z, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hin : ∀ (k : KG ε) (z : PCoord ε → ℂ), F (polarM (k, z)) * ENNReal.ofReal (Jac z) =
      ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    intro k z
    have hm : (polarM (k, z) : Fin n → Fin n → ℂ) ∈ S := polarM_inUJ (k, z)
    show S.piecewise f 0 (polarM (k, z)) * _ = _
    rw [Set.piecewise_eq_of_mem S f 0 hm]
    show ENNReal.ofReal (∑ i, ∑ l, c i l (polarM (k, z))) * _ = _
    rw [hval k z, ← ENNReal.ofReal_mul (hsOp_nonneg _)]
  let e : Formalism.REAL.UJ ε → (Fin n → Fin n → ℂ) := Formalism.MainNotions.S.umat
  let p : KG ε × (PCoord ε → ℂ) → (Fin n → Fin n → ℂ) := polarM
  let J : (PCoord ε → ℂ) → ENNReal := fun z => ENNReal.ofReal (Jac z)
  let ν := volume.withDensity J
  have he : MeasurableEmbedding e := (isClosedEmbedding_toM ε).measurableEmbedding
  have hp : Measurable p := (polarM_continuous ε).measurable
  have hJ : Measurable J := ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  have hrange : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range e := by
    change ∀ᵐ x ∂(Measure.map p ((dk ε).prod ν)), x ∈ Set.range e
    refine (ae_map_iff hp.aemeasurable he.measurableSet_range).2 (ae_of_all _ fun kz => ?_)
    show polarM kz ∈ Set.range (fun g : UJ ε => toM g)
    rw [range_toM]
    exact polarM_inUJ kz
  rw [hL]
  calc
    _ = ENNReal.ofReal (cPQ ε) * ∫⁻ x, F x ∂(muPolarMat ε) := by
      rw [muCD, lintegral_smul_measure, lintegral_comap_embedding he _ hrange F, smul_eq_mul]
    _ = ENNReal.ofReal (cPQ ε) * ∫⁻ kz, F (p kz) ∂((dk ε).prod ν) := by
      change _ * (∫⁻ x, F x ∂(Measure.map p ((dk ε).prod ν))) = _
      rw [lintegral_map hFm hp]
    _ = _ := by
      congr 1
      refine (lintegral_prod (μ := dk ε) (ν := ν) (F ∘ p) (hFm.comp hp).aemeasurable).trans ?_
      let I := ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z)
      calc
        _ = ∫⁻ _ : KG ε, I ∂(dk ε) := by
          refine lintegral_congr (fun k => ?_)
          refine (lintegral_withDensity_eq_lintegral_mul volume hJ
            (hFm.comp (hp.comp measurable_prodMk_left))).trans ?_
          exact lintegral_congr (fun z => (mul_comm (J z) (F (p (k, z)))).trans (hin k z))
        _ = I * dk ε Set.univ := lintegral_const I
        _ = I := by rw [haar_univ_eq_one, mul_one]

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

theorem sCoef_ge_one {lam : Fin n → ℝ} (hlam : Antitone lam) {i : ℕ} (hi : i + 1 < n) :
    1 ≤ sCoef lam i := by
  have h : lam ⟨i + 1, hi⟩ ≤ lam ⟨i, by omega⟩ := hlam (Fin.mk_le_mk.mpr (Nat.le_succ i))
  simp only [sCoef, dif_pos hi]
  linarith

theorem fi_scale {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    t * Fi (pmat z) i ≤ Fi ((t : ℂ) • pmat z) i := by
  have hc := fi_convex z hi
  have ht0 : 0 < t := by linarith
  have h : Fi (((1 / t * t + (1 - 1 / t) * 0 : ℝ) : ℂ) • pmat z) i ≤
      1 / t * Fi (((t : ℝ) : ℂ) • pmat z) i + (1 - 1 / t) * Fi (((0 : ℝ) : ℂ) • pmat z) i :=
    hc.2 (Set.mem_univ t) (Set.mem_univ (0 : ℝ)) (show (0 : ℝ) ≤ 1 / t by positivity)
      (show (0 : ℝ) ≤ 1 - 1 / t by rw [sub_nonneg, div_le_one ht0]; exact ht)
      (show 1 / t + (1 - 1 / t) = (1 : ℝ) by ring)
  have e1 : 1 / t * t + (1 - 1 / t) * 0 = 1 := by rw [mul_zero, add_zero, one_div_mul_cancel ht0.ne']
  have e0 : Fi (((0 : ℝ) : ℂ) • pmat z) i = 0 := by simp [fi_zero]
  rw [e1, e0, Complex.ofReal_one, one_smul, mul_zero, add_zero] at h
  calc t * Fi (pmat z) i ≤ t * (1 / t * Fi ((t : ℂ) • pmat z) i) := mul_le_mul_of_nonneg_left h ht0.le
    _ = Fi ((t : ℂ) • pmat z) i := by rw [← mul_assoc, mul_one_div_cancel ht0.ne', one_mul]

theorem ph_nonneg {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) :
    0 ≤ Ph lam (pmat z) := by
  unfold Ph
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  exact mul_nonneg (by linarith [sCoef_ge_one hlam hi']) (fi_nonneg z _)

theorem ph_scale {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) {t : ℝ}
    (ht : 1 ≤ t) : t * Ph lam (pmat z) ≤ Ph lam ((t : ℂ) • pmat z) := by
  unfold Ph
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  have hs := sCoef_ge_one hlam hi'
  have hf := fi_scale z (i := i + 1) (by omega) ht
  calc t * (sCoef lam i * Fi (pmat z) (i + 1)) = sCoef lam i * (t * Fi (pmat z) (i + 1)) := by ring
    _ ≤ sCoef lam i * Fi ((t : ℂ) • pmat z) (i + 1) := mul_le_mul_of_nonneg_left hf (by linarith)

theorem sum_Ico_sCoef (lam : Fin n → ℝ) {b a : ℕ} (hba : b ≤ a) (ha : a < n) :
    ∑ i ∈ Ico b a, sCoef lam i = lam ⟨b, by omega⟩ - lam ⟨a, ha⟩ + ((a : ℝ) - (b : ℝ)) := by
  induction a, hba using Nat.le_induction with
  | base => simp
  | succ k hbk ih =>
    rw [Finset.sum_Ico_succ_top hbk, ih (by omega)]
    simp only [sCoef, dif_pos ha]
    push_cast
    ring

theorem sum_Ico_sCoef_fin (lam : Fin n → ℝ) (a b : Fin n) (h : b ≤ a) :
    ∑ i ∈ Ico (b : ℕ) a, sCoef lam i = wab lam a b := by
  rw [sum_Ico_sCoef lam (Fin.le_iff_val_le_val.mp h) a.isLt]
  simp only [Fin.eta, wab]
  ring

theorem sum_sCoef_ind (lam : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i ∈ range (n - 1), sCoef lam i * (if (b : ℕ) < i + 1 ∧ i + 1 ≤ (a : ℕ) then c else 0) =
      if b < a then wab lam a b * c else 0 := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have ha := a.isLt
  have hf : (range (n - 1)).filter (fun i => (b : ℕ) < i + 1 ∧ i + 1 ≤ (a : ℕ)) = Ico (b : ℕ) a := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hf]
  split_ifs with h
  · rw [sum_Ico_sCoef_fin lam a b h.le]
  · have h' : (a : ℕ) ≤ b := Fin.le_iff_val_le_val.mp (not_lt.mp h)
    rw [Finset.Ico_eq_empty_of_le h', sum_empty, zero_mul]

theorem pmat_coord {ε : Fin n → Bool} (z : PCoord ε → ℂ) (ab : PCoord ε) :
    pmat z ab.1.1 ab.1.2 = z ab := by
  unfold pmat
  rw [dif_pos ab.2]

theorem sum_pairs_pmat {ε : Fin n → Bool} (w : Fin n → Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      ∑ ab : PCoord ε, w ab.1.1 ab.1.2 * ‖z ab‖ ^ 2 := by
  rw [← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2)]
  · rw [Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _ (by simp)]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [if_pos ab.2.1, pmat_coord]
  · intro x _ hx
    by_contra hP
    apply hx
    by_cases h1 : x.2 < x.1
    · have h2 : ε x.1 = ε x.2 := by
        by_contra h
        exact hP ⟨h1, h⟩
      have h3 : pmat z x.1 x.2 = 0 := by
        unfold pmat
        rw [dite_eq_right (fun h => h.2 h2), dite_eq_right (fun h => lt_asymm h.1 h1)]
      rw [if_pos h1, h3, norm_zero]
      ring
    · rw [if_neg h1]

theorem sum_sCoef_Vi {ε : Fin n → Bool} (lam : Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ i ∈ range (n - 1), sCoef lam i * Vi (pmat z) (i + 1) = Qf lam z := by
  have step1 : ∑ i ∈ range (n - 1), sCoef lam i * Vi (pmat z) (i + 1) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then wab lam a b * ‖pmat z a b‖ ^ 2 else 0 := by
    simp only [Vi, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact sum_sCoef_ind lam a b _
  rw [step1, ← Fintype.sum_prod_type', Qf]
  exact sum_pairs_pmat (wab lam) z

theorem ph_lower {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) {ep : ℝ}
    (h1 : rhoP z ≤ ep) (h2 : ep ≤ 1) : (1 - ep) * Qf lam z ≤ 2 * Ph lam (pmat z) := by
  rw [← sum_sCoef_Vi lam z, Ph, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  have hs := sCoef_ge_one hlam hi'
  have hf := fi_lower z (i := i + 1) (by omega) h1 h2
  have := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ sCoef lam i by linarith)
  nlinarith

end ReciprocityTheory.ChartRestriction.DS
end
end
