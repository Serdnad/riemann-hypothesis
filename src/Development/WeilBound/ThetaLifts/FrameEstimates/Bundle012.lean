module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle004
public import Development.WeilBound.ThetaLifts.FrameEstimates.RankIffRight
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle009
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_cols_det_ne_zero {K : Type} [Field K] {i d : ℕ} (A : Matrix (Fin i) (Fin d) K)
    (hA : LinearIndependent K A.row) : ∃ c : Fin i → Fin d, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = i := by
    rw [← finrank_span_eq_card hli, hsp, Matrix.rank_eq_finrank_span_cols, hA.rank_matrix, Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hu : IsUnit (A.submatrix id (a ∘ e)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem exists_one_le_emb {x : E} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : ∃ φ : E →+* ℂ, 1 ≤ ‖φ x‖ := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace E, 1 ≤ w x := by
    by_contra hne
    push Not at hne
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w) (a := (⟨x, hx⟩ : 𝓞 E))
      (fun h => h0 (congrArg Subtype.val h)) fun z _ => hne z) (not_le.2 (hne w))
  exact ⟨w.embedding, by rwa [InfinitePlace.norm_embedding_eq]⟩

theorem sum_lam_le_psum {d y : ℕ} {lam : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1 : ∀ i j, jx i ≠ jy j)
    (h2 : ∀ i t, lam (jx i) t = t i ∧ lam (jy i) t = -t i) (h3 : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam k = 0)
    {t : Fin y → ℝ} (ht : t ∈ Cone y) {i : ℕ} {c : Fin i → Fin d} (hc : Function.Injective c) :
    ∑ a, lam (c a) t ≤ psum t i := by
  classical
  have key : ∀ θ : ℝ, 0 ≤ θ → ∑ a, lam (c a) t ≤ ∑ j, max 0 (t j - θ) + i * θ := by
    intro θ hθ
    have e := sum_lam h1 h2 h3 (fun u => max 0 (u - θ)) t
    have e1 : ∀ j, max 0 (-t j - θ) = 0 := fun j => max_eq_left (by linarith [ht.2 j])
    simp only [e1, max_eq_left (show 0 - θ ≤ 0 by linarith), Finset.sum_const_zero, add_zero, mul_zero] at e
    rw [← e]
    have e2 : ∑ a, max 0 (lam (c a) t - θ) ≤ ∑ k, max 0 (lam k t - θ) := by
      exact (Finset.sum_map Finset.univ ⟨c, hc⟩ fun k => max 0 (lam k t - θ)).symm.trans_le
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => le_max_left _ _)
    have e3 : ∑ a, lam (c a) t ≤ ∑ a, (max 0 (lam (c a) t - θ) + θ) :=
      Finset.sum_le_sum fun a _ => by linarith [le_max_right 0 (lam (c a) t - θ)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e3
    linarith
  by_cases hi : i < y
  · refine (key (t ⟨i, hi⟩) (ht.2 _)).trans (le_of_eq ?_)
    have e : ∀ j : Fin y, max 0 (t j - t ⟨i, hi⟩) =
        (if j.val < i then t j else 0) - if j.val < i then t ⟨i, hi⟩ else 0 := by
      intro j
      split_ifs with h
      · exact max_eq_right (sub_nonneg.2 (ht.1 (show j ≤ ⟨i, hi⟩ from h.le)))
      · rw [sub_zero]
        exact max_eq_left (sub_nonpos.2 (ht.1 (show (⟨i, hi⟩ : Fin y) ≤ j from not_lt.1 h)))
    have hcard : (Finset.univ.filter fun j : Fin y => j.val < i).card = i := by
      rw [Fin.card_filter_val_lt]
      omega
    simp only [e, Finset.sum_sub_distrib]
    rw [← Finset.sum_filter (fun j : Fin y => j.val < i) fun _ => t ⟨i, hi⟩, Finset.sum_const, hcard, nsmul_eq_mul, psum]
    ring
  · refine (key 0 le_rfl).trans (le_of_eq ?_)
    rw [mul_zero, add_zero, psum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos (by omega), sub_zero, max_eq_right (ht.2 j)]

theorem psum_eq {q i : ℕ} (hi : i ≤ q) (s : Fin q → ℝ) : psum s i = ∑ a : Fin i, s (Fin.castLE hi a) := by
  exact (Fintype.sum_of_injective _ (Fin.castLE_injective hi) _ (fun j : Fin q => if j.val < i then s j else 0)
    (fun j hj => if_neg fun h => hj ⟨⟨j, h⟩, rfl⟩) fun a => (if_pos a.2).symm).symm

theorem minor_of : FrameBasis → Minor := by
  intro hB F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
  set A : ℝ := n.factorial * m * K with hA
  have hA1 : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm') hK
  refine ⟨A⁻¹, by positivity, fun s hs t ht x hx hsupp => ?_⟩
  obtain ⟨ha, hsz⟩ := h s t x
  have hint := ha hsupp
  have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set z := sz τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set ξ := (b⁻¹).1 * x * (b'⁻¹).1ᵀ with hξ
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (fr.r + 1) => psum s i.val - psum t i.val)
  have hiq : i.val ≤ fr.r := Nat.lt_succ_iff.1 i.2
  have hqn : fr.r ≤ n := by simpa using Fintype.card_le_of_embedding iy
  have hrk : ξ.rank = n := by
    rw [hξ, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by
      rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))]
    exact hx
  have hli : LinearIndependent E ξ.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← Matrix.rank_eq_finrank_span_row, hrk,
      Fintype.card_fin]
  let ρ : Fin i.val → Fin n := fun a => iy (Fin.castLE hiq a)
  obtain ⟨c, hc, hdet⟩ := exists_cols_det_ne_zero (ξ.submatrix ρ id)
    (hli.comp ρ (iy.injective.comp (Fin.castLE_injective hiq)))
  set M : Matrix (Fin i.val) (Fin i.val) E := (ξ.submatrix ρ id).submatrix id c with hM
  have hI : IsIntegral ℤ ((m : E) • M).det := IsIntegral.det fun a a' => hint _ _
  have hI0 : ((m : E) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hm.ne')) hdet
  obtain ⟨φ, hφ⟩ := exists_one_le_emb hI hI0
  obtain ⟨w, hw⟩ := norm_emb hσ τ φ
  rw [hw, Matrix.det_smul, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast,
    Fintype.card_fin] at hφ
  let N : Matrix (Fin i.val) (Fin i.val) ℂ := Matrix.of fun a a' =>
    (Real.exp (s (Fin.castLE hiq a)) : ℂ) * ((Real.exp (-lam' (c a') t) : ℂ) * (τ w).1 (M a a'))
  have hN : ‖N.det‖ = Real.exp (psum s i - ∑ a, lam' (c a) t) * ‖(τ w).1 M.det‖ := by
    have e1 : N.det = (∏ a, (Real.exp (s (Fin.castLE hiq a)) : ℂ)) * ((∏ a, (Real.exp (-lam' (c a) t) : ℂ)) *
        (τ w).1 M.det) := by
      rw [RingHom.map_det, ← Matrix.det_mul_row, ← Matrix.det_mul_column]
      rfl
    rw [e1, ← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Real.exp_sum, ← Real.exp_sum, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add, psum_eq hiq, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hent : ∀ a a', ‖N a a'‖ ≤ K * (1 + z) := by
    intro a a'
    let T : InfinitePlace F → Fin n → Fin d → ℝ := fun w k l => Real.exp (-(lam k s + lam' l t)) * ‖(τ w).1 (ξ k l)‖
    have hT : ∀ w k l, 0 ≤ T w k l := fun w k l => by positivity
    have e : ‖N a a'‖ = T w (ρ a) (c a') := by
      simp only [N, T, ρ, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        (h2 _ _).2, neg_add, neg_neg, Real.exp_add, mul_assoc]
      rfl
    have l1 := Finset.single_le_sum (f := T w (ρ a)) (fun _ _ => hT _ _ _) (Finset.mem_univ (c a'))
    have l2 := Finset.single_le_sum (f := fun k => ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ (ρ a))
    have l3 := Finset.single_le_sum (f := fun w => ∑ k, ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ w)
    have l4 : ∑ w, ∑ k, ∑ l, T w k l ≤ K * z := hsz
    linarith
  have hdle : ‖N.det‖ ≤ i.val.factorial * (K * (1 + z)) ^ i.val := by
    have := Matrix.det_le (A := N) (abv := NormedField.toAbsoluteValue ℂ) (x := K * (1 + z)) hent
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hv : Real.exp (viol s t) ≤ (A * (1 + z)) ^ (n + 1) := by
    have e1 : Real.exp (viol s t) ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) := by
      rw [viol, ← hi]
      exact Real.exp_le_exp.2 (by linarith [sum_lam_le_psum h1' h2' h3' ht hc])
    have hin : i.val ≤ n := hiq.trans hqn
    have e2 : (i.val.factorial : ℝ) ≤ (n.factorial : ℝ) ^ (n + 1) :=
      le_trans (by exact_mod_cast Nat.factorial_le hin) (le_self_pow₀ hf (by omega))
    have hB1 : 1 ≤ (m : ℝ) * (K * (1 + z)) :=
      one_le_mul_of_one_le_of_one_le hm' (one_le_mul_of_one_le_of_one_le hK (by linarith))
    calc _ ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) * ((m : ℝ) ^ i.val * ‖(τ w).1 M.det‖) :=
          e1.trans (le_mul_of_one_le_right (Real.exp_pos _).le hφ)
      _ = (m : ℝ) ^ i.val * ‖N.det‖ := by rw [hN]; ring
      _ ≤ (m : ℝ) ^ i.val * (i.val.factorial * (K * (1 + z)) ^ i.val) := by gcongr
      _ = i.val.factorial * ((m : ℝ) * (K * (1 + z))) ^ i.val := by rw [mul_pow (m : ℝ)]; ring
      _ ≤ (n.factorial : ℝ) ^ (n + 1) * ((m : ℝ) * (K * (1 + z))) ^ (n + 1) :=
          mul_le_mul e2 (pow_le_pow_right₀ hB1 (by omega)) (by positivity) (by positivity)
      _ = _ := by rw [← mul_pow, hA]; congr 1; ring
  rw [inv_mul_le_iff₀ (by positivity)]
  refine le_of_pow_le_pow_left₀ (n := n + 1) (by omega) (by positivity) ?_
  rw [← Real.exp_nat_mul, show ((n + 1 : ℕ) : ℝ) * (viol s t / (n + 1)) = viol s t by push_cast; field_simp]
  exact hv

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem sq_iff {a P L : ℝ≥0∞} : a ^ 2 ≤ P ^ 2 * L ↔ a ≤ P * L ^ (1 / 2 : ℝ) := by
  have e : L = (L ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  conv_lhs => rw [e, ← mul_pow]
  exact ⟨fun h => (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h, fun h => by gcongr⟩

theorem latSum_mono {τ : ∀ w : InfinitePlace F, EmbOver E w} {C C' : Set (Ten F E n d)} (hC : C ⊆ C') (N : ℕ) (S)
    (g : UA σ X.J) (h : UA σ W.J) : latSum τ C N S g h ≤ latSum τ C' N S g h := by
  refine ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_
  by_cases hx : ∃ c ∈ C, At (evI F) (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ - c)
  · obtain ⟨c, h1, h2⟩ := hx
    unfold maj
    rw [if_pos ⟨c, h1, h2⟩, if_pos ⟨c, hC h1, h2⟩]
  · conv_lhs => unfold maj
    rw [if_neg hx]
    exact sq_maj_nonneg _ _ _ _


variable (B om) in
def Qb (N : ℕ) (Φ : SInf F (Fin n × Fin d) → Fn F n d) : Prop :=
  (∀ f, Φ f ∈ schA F (Fin n × Fin d)) ∧ ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧
    IsCompact C ∧ ∀ f g h, ‖theta om (Φ f) g h‖ₑ ^ 2 ≤ ENNReal.ofReal (p f) ^ 2 * latSum B.emb C N (fullRank E n d) g h

theorem qb_zero (N : ℕ) : Qb B om N fun _ => 0 :=
  ⟨fun _ => zero_mem _, 0, ∅, continuous_const, isCompact_empty, fun f g h => by simp [theta, thetaSum]⟩

theorem Qb.add (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ Ψ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (h2 : Qb B om N Ψ) : Qb B om N fun f => Φ f + Ψ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  obtain ⟨a2, q, C', b2, c2, d2⟩ := h2
  refine ⟨fun f => add_mem (a1 f) (a2 f), p + q, C ∪ C', (b1.add b2 : Continuous fun f => p f + q f), c1.union c2,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 ((d1 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_left N _ g h) _))
  have e2 := sq_iff.1 ((d2 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_right N _ g h) _))
  rw [theta_add hp (a1 f) (a2 f), Seminorm.add_apply, ENNReal.ofReal_add (apply_nonneg p f) (apply_nonneg q f), add_mul]
  exact (enorm_add_le _ _).trans (add_le_add e1 e2)

theorem Qb.smul (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (c : ℂ) : Qb B om N fun f => c • Φ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  refine ⟨fun f => Submodule.smul_mem _ _ (a1 f), ‖c‖₊ • p, C, (continuous_const.mul b1 : Continuous fun f => ‖c‖ * p f), c1,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 (d1 f g h)
  rw [theta_smul hp c (a1 f), enorm_mul, show (‖c‖₊ • p) f = ‖c‖ * p f from rfl, ENNReal.ofReal_mul (norm_nonneg c),
    ofReal_norm, mul_assoc]
  exact mul_le_mul_right e1 _

theorem qb_sum (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {ι : Type} (S : Finset ι)
    {Φ : ι → SInf F (Fin n × Fin d) → Fn F n d} (h : ∀ i, Qb B om N (Φ i)) : Qb B om N fun f => ∑ i ∈ S, Φ i f := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using qb_zero N
  | insert a S ha ih => simpa [Finset.sum_insert ha] using (h a).add hp ih

theorem thetaSum_neg {κ : Type} (Φ : (κ → AF F) → ℂ) : thetaSum F (fun x => Φ (-x)) = thetaSum F Φ := by
  unfold thetaSum
  rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun ξ => congrArg Φ (funext fun i => ?_)
  simp

theorem theta_neg (hP : Parity) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (g h) :
    theta om (fun x => Φ (-x)) g h = theta om Φ g h := by
  obtain ⟨e, c, he, hc, h1⟩ := hP F E σ B n d X W M χX χW om r s r' s' hp
  have hc0 : c ≠ 0 := fun h0 => by simp [h0] at hc
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h) Φ hΦ
  have hcomm : g * e = e * g := Subtype.ext (Units.ext (by
    change mat g * mat e = mat e * mat g
    rw [he]; simp))
  have e1 : om (g, h) (om (e, 1) Φ) = om (e, 1) (om (g, h) Φ) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, hcomm, mul_one,
      one_mul]
  rw [h1 Φ hΦ, h1 _ hs, map_smul] at e1
  unfold theta
  rw [smul_right_injective _ hc0 e1, thetaSum_neg]



open scoped Classical in
theorem qb_piece (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) (hp : IsPair B M χX χW om r s r' s') (N : ℕ)
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB _)
    (h0 : ∀ (f : SInf F (Fin n × Fin d)) (μ : Measure (Fin n × Fin d → AF F)), μ.IsAddHaarMeasure → ∀ z : Ten F E n d,
      (z.map (piW (B.τ₁.comp σ))).rank ≠ n → coef F B.ψ μ (pureA F f φ) (fun x => pureA F f φ (-x)) (M.co.e z) = 0) :
    Qb B om N fun f => pureA F f φ := by
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  have hφ' : (fun y => φ (-y)) ∈ SB (Fin n × Fin d → Af F) :=
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ _ hφ' N
  let P : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)
  have hPf : ∀ f : SInf F (Fin n × Fin d), (fun x => pureA F f φ (-x)) = pureA F (P f) fun y => φ (-y) := fun f => by
    funext x
    unfold pureA
    congr 1
    exact congrArg f (funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1)
  let q : Seminorm ℂ (SInf F (Fin n × Fin d)) := p + p.comp P.toLinearMap
  have hq : Continuous q := (hpc.add (hpc.comp P.continuous) : Continuous fun f => p f + p (P f))
  refine ⟨fun f => pureA_mem f hφ, NNReal.mk √c (Real.sqrt_nonneg c) • q, C,
    (continuous_const.mul hq : Continuous fun f => √c * q f), hC, fun f g h => ?_⟩
  have hm := pureA_mem f hφ
  have e := h1 _ hm _ (ParityOfCoefficients.neg_mem_schA hm) g h
  rw [theta_neg hP hp hm] at e
  refine sq_le_of_coef hc (apply_nonneg q f) e (fun x hx => h0 f μ hμ _ fun hr => hx ?_) fun x => ?_
  · rw [Matrix.map_mul, Matrix.map_mul, ThKEst.W.incM_piW] at hr
    have hr2 := ThKEst.W.rank_of_mul _ _ _ hr
    exact ThKEst.W.rank_of_map (B.τ₁.comp σ).toRingHom x hr2
  · rw [hPf]
    refine (h2 f (P f) _).trans (mul_le_mul_of_nonneg_right ?_ (sq_maj_nonneg _ _ _ _))
    have a1 := apply_nonneg p f
    have a2 := apply_nonneg p (P f)
    change p f * p (P f) ≤ (p f + p (P f)) * (p f + p (P f))
    nlinarith

end

theorem sqSo_of' (hF : SoFin) (hC : SoCut) (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqSo := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨m, c, χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.2.2 φ hφ
  have key : Qb B om N fun f => ∑ i, c i • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i) := qb_sum hp _ fun i => Qb.smul hp (c := c i) <| by
    obtain ⟨k, ξ, e1, hξ⟩ := hC F E σ B n d X W M χX χW om r s r' s' hp _ (hχ i).2.2
    have hstd : ∀ᶠ u in cofinite, χ i u = ThKEst.W.stdF _ u := ((hχ i).2.1.and hp.good.std).mono fun v hv => hv.1.trans hv.2
    have hg : ThKEst.W.Good (χ i) := ⟨(hχ i).1, hstd⟩
    have e2 : (fun f : SInf F (Fin n × Fin d) => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i)) =
        fun f : SInf F (Fin n × Fin d) => ∑ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) := funext fun f => by
      conv_lhs => rw [← Function.update_eq_self B.v₁ (χ i), ThKEst.W.pure_update (v := B.v₁) f hstd, e1]
      have e3 : ∀ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) =
          tens (evFin F B.v₁) (ξ j) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update (χ i) B.v₁ 1)) := fun j =>
        ThKEst.W.pure_update (v := B.v₁) f hstd (ξ j)
      rw [Finset.sum_congr rfl fun j _ => e3 j]
      funext x
      rw [Finset.sum_apply]
      unfold tens
      rw [Finset.sum_apply, Finset.sum_mul]
    rw [e2]
    refine qb_sum hp _ fun j => qb_piece hP hS hE hB hp N (ThKEst.W.pf_mem (hg.update (hξ j).1.1)) fun f μ hμ z hz => ?_
    rw [← ThKEst.W.pure_eq, ThKEst.W.pure_update (v := B.v₁) f hstd]
    refine (hξ j).2 _ ⟨fun x z hz => ?_, ?_⟩ μ hμ z hz
    · have h1 := (ThKEst.W.at_iff (v := B.v₁) z).1 hz
      have h2 : z = fun i => GlobalTheory.EmbChart.atPlace B.v₁ (evFin F B.v₁ (z i)) := funext fun i =>
        (congrFun h1 i).symm.trans (ThKEst.W.ep_mul (v := B.v₁) (z i))
      rw [h2]
      exact ThKEst.W.indep_pure (v := B.v₁) f (χ i) x _
    · rw [← ThKEst.W.pure_update (v := B.v₁) f hstd]
      exact ThKEst.W.pure_mem f (hg.update (hξ j).1.1)
  obtain ⟨-, p, C, h1, h2, h3⟩ := key
  exact ⟨p, C, h1, h2, fun f g h => by rw [e f]; exact h3 f g h⟩

end PositivityTheory.ThKEst

end
end
