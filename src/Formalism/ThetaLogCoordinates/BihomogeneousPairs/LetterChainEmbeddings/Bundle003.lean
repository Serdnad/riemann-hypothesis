module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.Bundle001
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct
public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.SmulMemOfNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality

section tieop
variable {p : ℕ} [Fact p.Prime]

theorem int_Fpow {τ : Type} {r : ℕ} (L m : ℕ) (hmL : Nat.log p m ≤ L) (w e : Fin r → τ)
    {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) y) ∈ IntPol p τ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  set Mc : ℝ := (p : ℝ) ^ L with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ m, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hmL))
  let Dc : Fin r → (MvPolynomial τ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial τ ℚ_[p]) (MvPolynomial τ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (Dc a) (Dc b) := by
    intro a b
    simp only [Dc, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum Dc hcomm (fun a k => contr_D _ _ k) hM1 m hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, Dc c := rfl
  have hb : Bnd (p := p) 1 y := (intPol_iff_bnd y).mp hy
  have h1 := hF m le_rfl 1 zero_le_one y hb
  rw [← hFeq] at h1
  rw [intPol_iff_bnd, ← smul_smul]
  have h2 := bnd_smul ((p : ℚ_[p]) ^ (r * L)) h1
  intro μ
  refine (h2 μ).trans (le_of_eq ?_)
  rw [Padic.norm_p_pow, hMc, one_mul, ← pow_mul, zpow_neg, zpow_natCast, mul_comm L r]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by positivity))

variable {N r : ℕ} [NeZero r] {D : BlockData N}

theorem xi_free {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {v : BVar N r D.T.t} (hv : ∀ c, v ≠ xiVar N r D.T.t c) : pderiv v g = 0 :=
  ProjS.pderiv_of_free v g (fun m hm => (xi_supp hg hm).1 v hv)

theorem tieF_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) :
    tieF (wv D i) (ev D i) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y) * g := by

  rw [tieF_apply', tieF_apply', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_mul, he c, mul_zero, add_zero, ev_chain hB, pderiv_rename chainEmb_inj, pderiv_mul, hw c,
    mul_zero, add_zero, wv_chain hB, pderiv_rename chainEmb_inj]

theorem tieF_pow_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) (m : ℕ) :
    (tieF (wv D i) (ev D i) ^ m) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        ((tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y) * g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, tieF_gen hB i _ g hw he, ← Module.End.mul_apply, ← pow_succ']

omit [NeZero r] in
theorem update_single (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (m : ℕ) :
    Function.update (j + Pi.single i m : Fin D.T.t → ℕ) i ((j + Pi.single i m : Fin D.T.t → ℕ) i + 1) =
      j + Pi.single i (m + 1) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp; ring
  · simp [hk]

theorem Y_iter (hF : HypJoin p (r := r) D) (i : Fin D.T.t) :
    ∀ m (j : Fin D.T.t → ℕ) (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y ∈
        Y p (r := r) (D.lettersAt (j + Pi.single i m) jp) D.T.J D.T.thr := by
  intro m
  induction m with
  | zero =>
    intro j jp y hy
    have h0 : j + Pi.single i 0 = j := by simp
    rw [h0, pow_zero, Module.End.one_apply]
    exact hy
  | succ m ih =>
    intro j jp y hy
    have h := hF _ jp i _ (ih j jp y hy)
    rw [update_single] at h
    rw [pow_succ', Module.End.mul_apply]
    exact h

theorem lat_tie (hB : D.BlockOK) (hF : HypJoin p (r := r) D) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t)
    (m L : ℕ) (hmL : Nat.log p m ≤ L) :
    ∀ x ∈ Lat p D (r := r) j jp, (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) •
      (tieF (wv D i) (ev D i) ^ m) x) ∈ Lat p D (r := r) (j + Pi.single i m) jp := by
  intro x hx
  have := span_map_mem ((((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹)) •
    (tieF (wv D i) (ev D i) ^ m)) _ (Lat p D (r := r) (j + Pi.single i m) jp) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  rw [LinearMap.smul_apply, tieF_pow_gen hB i y g
    (fun c => xi_free hg (fun d => wv_ne_xi hB i c d)) (fun c => xi_free hg (fun d => ev_ne_xi hB i c d)),
    ← smul_mul_assoc, ← map_smul]
  refine Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (Y_iter hF i m j jp y (yz_y hy)))
    (int_Fpow L m hmL _ _ (yz_int hy)), g, hg, rfl⟩

end tieop

theorem lattice_equal_holds : LatTie := by
  intro p _ N r _ D hB hF j jp i m L hmL x hx
  exact lat_tie hB hF j jp i m L hmL x hx

end Formalism.InvariantFactorPaths.KP.LL
end

section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

theorem tieP_smul {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k)
    (y : MvPolynomial σ k) : tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [mul_smul_comm, map_smul, map_smul, smul_comm]

theorem pst_scal_mem {p : ℕ} [Fact p.Prime] {σ : Type} (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (a u m j k : ℕ) (hk : k ≤ j) (hu : a + Nat.log p j ≤ u) (s : ℚ_[p]) (hs : ‖s‖ ≤ 1)
    (y : MvPolynomial σ ℚ_[p])
    (hy : (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) ∈ Λ) :
    ((s * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y) ∈ Λ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp1
  have e1 : (s * (p : ℚ_[p]) ^ (a + Nat.log p j + d) *
      (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y =
      (s * (p : ℚ_[p]) ^ d * ((p : ℚ_[p]) ^ (Nat.log p j) * (((j.choose k : ℕ) : ℚ_[p]))⁻¹)) •
        (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) := by
    rw [smul_smul, mul_inv, pow_add, pow_add]
    congr 1
    ring
  rw [e1]
  refine smul_mem_of_norm Λ ?_ hy
  have hpn : ∀ t : ℕ, ‖(p : ℚ_[p]) ^ t‖ = ((p : ℝ) ^ t)⁻¹ := by
    intro t
    rw [norm_pow, Padic.norm_p, inv_pow]
  rw [norm_mul, norm_mul, norm_mul, hpn, hpn]
  have h1 : ((p : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
  have h2 : ((p : ℝ) ^ (Nat.log p j))⁻¹ * ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ 1 := by
    have := PhiIntegrality.norm_choose_inv_le (p := p) j k hk
    rw [inv_mul_le_iff₀ (pow_pos hp0 _), mul_one]
    exact this
  have h3 : ‖s‖ * ((p : ℝ) ^ d)⁻¹ ≤ 1 :=
    mul_le_one₀ hs (inv_nonneg.mpr (pow_pos hp0 _).le) h1
  exact mul_le_one₀ h3 (mul_nonneg (inv_nonneg.mpr (pow_pos hp0 _).le) (norm_nonneg _)) h2

theorem pair_induction_holds : PairStep := by
  intro p _ σ r w e zv sv hr hz o n z L u Λ h1 h2 hu l hl x hx
  constructor
  · rw [decomp w e zv sv hr hz (o - l) (n - l) z x (h1 l x hx), Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    simp only [mem_range] at hm
    refine Submodule.subset_span ⟨l + m, by omega,
      ((1 : ℚ_[p]) * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
        (((o - l + (n - l) + r + z - m).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
    · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ 1 (by simp) _ (h2 l m (by omega) x hx)
      exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
    · rw [Nat.sub_sub, Nat.sub_sub, one_mul, mul_smul, tieP_smul w e zv sv _ _ _ ((p : ℚ_[p]) ^ u),
        mul_smul_comm, pow_add, mul_assoc]
  · rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    by_cases hmm : min (o - l) (n - l) < m
    · rw [h1 l x hx m hmm]
      simp
    · refine Submodule.subset_span ⟨l + m, by omega,
        ((-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
          (((o - l + (n - l) + r + z - 1).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
      · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ _ (by simp) _ (h2 l m (by omega) x hx)
        exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
      · simp only [smul_eq_C_mul, div_eq_mul_inv, map_mul]
        ring

end Formalism.InvariantFactorPaths.KP.LL
end
