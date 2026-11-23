module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
public import Formalism.RealPlaceAnalysis.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HasDerivAtInvExpCurveEntry
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lfD_cnt (P : Fin n → Prop) [DecidablePred P] {a b : Fin n} (hab : a < b) :
    (univ.filter fun c => a < c ∧ P c).card + (univ.filter fun c => c < b ∧ P c).card =
      (univ.filter fun c => c < a ∧ P c).card + (univ.filter fun c => b < c ∧ P c).card +
        2 * (univ.filter fun c => a < c ∧ c < b ∧ P c).card +
        (univ.filter fun c => c = a ∧ P c).card + (univ.filter fun c => c = b ∧ P c).card := by
  have key : ∀ c : Fin n, ((if a < c ∧ P c then 1 else 0) + (if c < b ∧ P c then 1 else 0) : ℕ) =
      (if c < a ∧ P c then 1 else 0) + (if b < c ∧ P c then 1 else 0) +
        2 * (if a < c ∧ c < b ∧ P c then 1 else 0) + (if c = a ∧ P c then 1 else 0) +
        (if c = b ∧ P c then 1 else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | rfl | hac
    · have h1 : ¬ a < c := not_lt_of_gt hca
      have h2 : c < b := hca.trans hab
      have h3 : ¬ b < c := not_lt_of_gt h2
      have h4 : c ≠ a := hca.ne
      have h5 : c ≠ b := h2.ne
      by_cases hP : P c <;> simp [h1, h2, h3, h4, h5, hca, hP]
    · have h3 : ¬ b < c := not_lt_of_gt hab
      have h5 : c ≠ b := hab.ne
      by_cases hP : P c <;> simp [hab, h3, h5, hP]
    · rcases lt_trichotomy c b with hcb | rfl | hbc
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h3 : ¬ b < c := not_lt_of_gt hcb
        have h4 : c ≠ a := hac.ne'
        have h5 : c ≠ b := hcb.ne
        by_cases hP : P c <;> simp [hac, hcb, h1, h3, h4, h5, hP]
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h4 : c ≠ a := hac.ne'
        by_cases hP : P c <;> simp [hac, h1, h4, hP]
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h2 : ¬ c < b := not_lt_of_gt hbc
        have h4 : c ≠ a := hac.ne'
        have h5 : c ≠ b := hbc.ne'
        by_cases hP : P c <;> simp [hac, hbc, h1, h2, h4, h5, hP]
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => key c)

theorem lfD_single (P : Fin n → Prop) [DecidablePred P] (a : Fin n) :
    (univ.filter fun c => c = a ∧ P c).card = if P a then 1 else 0 := by
  rw [Finset.card_filter, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem lf_rhoN_sub_nat (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ∃ m : ℕ, rhoN ε a - rhoN ε b = m := by
  refine ⟨(univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card, ?_⟩
  have hc := lfD_cnt (fun c => ε c ≠ ε a) hab
  rw [lfD_single, lfD_single, if_neg (fun h => h rfl), if_neg (fun h => h he.symm)] at hc
  have hr := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hr
  simp only [rhoN, ← he]
  linarith

theorem lf_rhoHol_eq (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) : rhoHol ε a = rhoHol ε b := by
  simp only [rhoHol, he]

theorem lf_dom {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {M : Type*} [AddCommGroup M]
    [Module ℂ M] {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F (lowK ε lam) V) :
    ∀ a b, a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a := by
  suffices H : ∀ d, ∀ a b : Fin n, b.val - a.val = d → a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a by
    intro a b hab he
    exact H _ a b rfl hab he
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a b hd hab he
    by_cases hmid : ∃ c, a < c ∧ c < b ∧ ε c = ε a
    · obtain ⟨c, hac, hcb, hce⟩ := hmid
      have hac' := Fin.lt_def.mp hac
      have hcb' := Fin.lt_def.mp hcb
      have h1 := ih (c.val - a.val) (by omega) a c rfl hac hce.symm
      have h2 := ih (b.val - c.val) (by omega) c b rfl hcb (hce.trans he)
      exact h2.trans h1
    · simp only [not_exists, not_and] at hmid
      have hC := HW.rhoC_consec ε hab he hmid
      obtain ⟨m, hm⟩ := HW.kIrrHW_int ε hF hV a b hab he
      obtain ⟨k, hk⟩ := lf_rhoN_sub_nat ε hab he
      have hH := lf_rhoHol_eq ε he
      have hl := hlam hab
      have hlk : lowK ε lam a - lowK ε lam b =
          lam a - lam b + (rhoN ε a - rhoN ε b) - (rhoC ε a - rhoC ε b) := by
        simp only [lowK, Pi.add_apply, Pi.sub_apply]
        ring
      have hkm : (k : ℝ) < m + 1 := by linarith
      have hkm' : k < m + 1 := by exact_mod_cast hkm
      have hkm'' : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp hkm'
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

theorem tensor_group_mul_kDiag (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ (g * k) f = tensGrp dual σ g (kDiag dual σ k f) := by
  obtain ⟨hu, hkJ⟩ := hk
  have hkk : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hkU : k ∈ UJset ε := by
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hσ' : σ (g * k) = (σ g).comp (σ k) := hσ.1.2 g hg k hkU
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
  funext c

  simp only [tensGrp, kDiag, hσ', ContinuousLinearMap.comp_apply, map_sum, map_smul, Finset.smul_sum,
  smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  cases dual
  · simp [Matrix.mul_apply]
  · simp only [cond_true]
    rw [Matrix.mul_inv_rev, hkinv, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun e _ => by rw [Matrix.conjTranspose_apply, mul_comm]

theorem tensor_phi_of_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (dual : Bool) (c d : Fin n) :
    oa1Phi dual g c d =
      cond dual ((if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1)) (g c d) := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  cases dual
  · rfl
  · have hJJ : Jm ε * Jm ε = 1 := by
      rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      split_ifs <;> norm_num
    have hinv : g⁻¹ = Jm ε * gᴴ * Jm ε := Matrix.inv_eq_left_inv (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJJ])
    simp only [oa1Phi, cond_true]
    rw [hinv]
    simp [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

theorem norm_tensor_phi_le_sqrt_hs {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (dual : Bool) (c d : Fin n) :
    ‖oa1Phi dual g c d‖ ≤ Real.sqrt (S7.hs g) := by
  have hent : ‖g c d‖ ≤ Real.sqrt (S7.hs g) := by
    have h1 : ‖g c d‖ ^ 2 ≤ ∑ j', ‖g c j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖g c j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ d)
    have h2 : ∑ j', ‖g c j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ c)
    have h3 : ‖g c d‖ ^ 2 ≤ S7.hs g := by
      simp only [S7.hs, Formalism.REAL.hs]
      exact h1.trans h2
    have h4 := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at h4
  rw [tensor_phi_of_unitary hg dual c d]
  cases dual
  · exact hent
  · have hb : ∀ b : Bool, ‖(if b then (1 : ℂ) else -1)‖ = 1 := by
      intro b
      cases b <;> simp
    simp only [cond_true, norm_mul, norm_star]
    rw [hb, hb, one_mul, mul_one]
    exact hent

theorem smoothOnG_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i ∈ s, Formalism.REAL.SmoothOnG ε (F i)) : Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, F i x) := by
  unfold Formalism.REAL.SmoothOnG at h ⊢
  intro g₀ hg₀
  choose! U F hU hgU hF hFU using fun i (hi : i ∈ s) => h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, F i x, isOpen_biInter_finset fun i hi => hU i hi,
    Set.mem_iInter₂.2 fun i hi => hgU i hi,
    ContDiffOn.sum fun i hi => (hF i hi).mono (Set.biInter_subset_of_mem hi), fun g hg hgJ => ?_⟩
  exact Finset.sum_congr rfl fun i hi => hFU i hi g (Set.mem_iInter₂.1 hg i hi) hgJ

theorem smoothOnG_inner_rep (w : H) {v : H} (hv : IsSmoothVecU ε σ v) :
    Formalism.REAL.SmoothOnG ε (fun g => inner ℂ w (σ g v)) := by
  unfold IsSmoothVecU S7.SmoothOnGV at hv
  unfold Formalism.REAL.SmoothOnG
  intro g₀ h₀
  obtain ⟨U, F, hU, h0U, hF, hFU⟩ := hv g₀ h₀
  refine ⟨U, fun g => inner ℂ w (F g), hU, h0U, contDiffOn_const.inner ℂ hF, fun g hg hgJ => ?_⟩
  simp only [hFU g hg hgJ]

theorem smoothOnG_tensor_phi (dual : Bool) (c d : Fin n) : Formalism.REAL.SmoothOnG ε (fun g => oa1Phi dual g c d) := by
  have hent : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g c d) := by
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun M => M c d, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have hst : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => star (g c d)) := by
    let L' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun M => star (M c d)
        map_add' := fun _ _ => by simp
        map_smul' := fun r M => by simp [Complex.real_smul, Complex.conj_ofReal] <;> ring }
    exact (LinearMap.toContinuousLinearMap L').contDiff
  unfold Formalism.REAL.SmoothOnG
  intro g₀ _
  cases dual
  · exact ⟨Set.univ, fun g => g c d, isOpen_univ, trivial, hent.contDiffOn, fun g _ _ => rfl⟩
  · refine ⟨Set.univ, fun g => (if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1),
      isOpen_univ, trivial, ((contDiff_const.mul hst).mul contDiff_const).contDiffOn, fun g _ hg => ?_⟩
    beta_reduce
    rw [tensor_phi_of_unitary hg true c d]
    rfl

private lemma smoothOnG_mul {f g : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    (hg : Formalism.REAL.SmoothOnG ε g) : Formalism.REAL.SmoothOnG ε (fun x => f x * g x) := by
  unfold Formalism.REAL.SmoothOnG at hf hg ⊢
  intro g₀ h₀
  obtain ⟨U, F, hU, h0U, hF, hFU⟩ := hf g₀ h₀
  obtain ⟨V, G, hV, h0V, hG, hGV⟩ := hg g₀ h₀
  refine ⟨U ∩ V, fun x => F x * G x, hU.inter hV, ⟨h0U, h0V⟩,
    (hF.mono Set.inter_subset_left).mul (hG.mono Set.inter_subset_right), fun x hx hxJ => ?_⟩
  simp only [hFU x hx.1 hxJ, hGV x hx.2 hxJ]

theorem tensor_coef_smooth (dual : Bool) (η f : Fin n → H) (hf : ∀ d, IsSmoothVecU ε σ (f d)) :
    Formalism.REAL.SmoothOnG ε (fun g => ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)) := by
  have heq : (fun g => ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)) =
      fun g => ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d)) := by
    funext g
    simp only [tensGrp, inner_sum, inner_smul_right, oa1Phi]
  rw [heq]
  exact smoothOnG_finset_sum univ (fun c g => ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d))) fun c _ =>
    smoothOnG_finset_sum univ (fun d g => oa1Phi dual g c d * inner ℂ (η c) (σ g (f d))) fun d _ =>
      smoothOnG_mul (smoothOnG_tensor_phi dual c d) (smoothOnG_inner_rep (η c) (hf d))

theorem continuous_umat' : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_rep_orbit (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := (hσ.2.2 v).comp_continuous continuous_umat' fun g => g.2

theorem continuous_tensor_phi (dual : Bool) (c d : Fin n) :
    Continuous (fun g : Formalism.REAL.UJ ε => oa1Phi dual (Formalism.MainNotions.S.umat g) c d) := by
  have he : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g c d) :=
    (continuous_apply d).comp ((continuous_apply c).comp continuous_umat')
  cases dual
  · exact he
  · have hfun : (fun g : Formalism.REAL.UJ ε => oa1Phi true (Formalism.MainNotions.S.umat g) c d) = fun g =>
        (if ε d then (1 : ℂ) else -1) * star (Formalism.MainNotions.S.umat g c d) * (if ε c then (1 : ℂ) else -1) := by
      funext g
      rw [tensor_phi_of_unitary (g := Formalism.MainNotions.S.umat g) (show inUJ ε (Formalism.MainNotions.S.umat g) from g.2) true c d]
      rfl
    rw [hfun]
    exact (continuous_const.mul he.star).mul continuous_const

theorem tensor_term_memLp (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (dual : Bool) {w v : D} (hw : w ∈ S) (hv : v ∈ S) (c d : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      oa1Phi dual (Formalism.MainNotions.S.umat g) c d * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε) := by
  refine MemLp.of_le (hW v hv w hw) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner (continuous_rep_orbit hσ _))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (norm_tensor_phi_le_sqrt_hs (show inUJ ε (Formalism.MainNotions.S.umat g) from g.2) dual c d) (norm_nonneg _)

theorem tensor_coef_memLp (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (η f : Fin n → D) (hη : η ∈ tensSub S) (hf : f ∈ tensSub S) :
    MemLp (fun g : Formalism.REAL.UJ ε => ∑ c, inner ℂ ((η c : D) : H)
      (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun c => ((f c : D) : H)) c)) 2 (Formalism.REAL.muG ε) := by
  have e : (fun g : Formalism.REAL.UJ ε => ∑ c, inner ℂ ((η c : D) : H)
      (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun c => ((f c : D) : H)) c)) = fun g =>
      ∑ c, ∑ d, oa1Phi dual (Formalism.MainNotions.S.umat g) c d *
        inner ℂ ((η c : D) : H) (σ (Formalism.MainNotions.S.umat g) ((f d : D) : H)) :=
    funext fun g => tensor_coef_expand dual σ _ _ _
  rw [e]
  rw [tset_mem] at hη hf
  exact memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => tensor_term_memLp hσ hW dual (hη c) (hf d) c d

end ReciprocityTheory.ChartRestriction.DS
end
end
