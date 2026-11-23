module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingEqIntegralAddEisensteinFiltration
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Et.kerL_eq_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  intro F E _ _ _ _ _ A ψ x r j hj y' y
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  haveI : Module.Finite E A.L := Module.Finite.equiv j.symm
  haveI : Module.Free E A.L := Module.Free.of_equiv j.symm
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hb.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hb.equiv
  rw [hj y' y]
  unfold Et.kerL Et.psiK
  congr 1
  rw [← Algebra.smul_def, smul_mul_assoc, Algebra.trace_trace (R := F) (S := E), ← smul_eq_mul,
    ← LinearMap.map_smul, Algebra.trace_trace]
end GlobalTheory.JR
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_tower_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (z : A.L), Algebra.trace F A.K (Algebra.trace A.K A.L z) = Algebra.trace F E (Algebra.trace E A.L z) := by
  intro F E _ _ _ _ hU A z
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  have hE : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap := A.push.out
  have hK : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free E A.L := Module.Free.of_equiv hE.equiv
  haveI : Module.Finite E A.L := Module.Finite.equiv hE.equiv
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hK.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hK.equiv
  rw [Algebra.trace_trace, Algebra.trace_trace]

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SLGen

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle x hx1
  rw [h, norm_zero] at this
  linarith

variable {F : Type} [Field F]

theorem nS_coe (z : F) : ((nS z : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, z; 0, 1] := rfl

theorem wS_coe : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem wS_inv_coe :
    (((wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, wS_coe, Matrix.adjugate_fin_two]; simp

theorem diag_coe {ϖ : F} (hϖ : ϖ ≠ 0) :
    ((nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![ϖ, 0; 0, ϖ⁻¹] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hϖ] <;> field_simp <;> ring

theorem conj_step {ϖ : F} (hϖ : ϖ ≠ 0) (t : F) :
    (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹)⁻¹ * nS t *
      (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹) = nS (ϖ⁻¹ ^ 2 * t) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, diag_coe hϖ, nS_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem decomp (g : SpecialLinearGroup (Fin 2) F) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    g = nS (((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      ((wS F)⁻¹ * nS (-(g : Matrix (Fin 2) (Fin 2) F) 1 0) * wS F) *
      nS (((g : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination -hdet | linear_combination -2 * hdet | linear_combination hdet |
      linear_combination 2 * hdet

theorem eq_top_of (H : Subgroup (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ H) (hn : ∀ t, nS t ∈ H) :
    H = ⊤ := by
  have hl : ∀ c : F, (wS F)⁻¹ * nS (-c) * wS F ∈ H := fun c =>
    H.mul_mem (H.mul_mem (H.inv_mem hw) (hn _)) hw
  have key : ∀ g : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    rw [decomp g hc]
    exact H.mul_mem (H.mul_mem (hn _) (hl _)) (hn _)
  rw [eq_top_iff]
  intro g _
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := g.2
    rw [Matrix.det_fin_two, hc] at hdet
    have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h; rw [h] at hdet; simp at hdet
    set L1 : SpecialLinearGroup (Fin 2) F := (wS F)⁻¹ * nS (-(1 : F)) * wS F
    have h1 : L1 * g ∈ H := by
      apply key
      simp only [L1, Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, ha]
    have : g = L1⁻¹ * (L1 * g) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem (hl 1)) h1
  · exact key g hc

end GlobalTheory.JR.SLGen


open GlobalTheory.JR.SLGen in
theorem GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  set H := Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t})
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_unif F
  have hw : wS F ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hS : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ H := fun t ht =>
    Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)
  have hball : ∀ t : F, ‖t‖ ≤ 1 → nS t ∈ H := fun t ht => hS t fun y hy => by
    rw [norm_mul]; nlinarith [norm_nonneg t, norm_nonneg y]
  have hinv : nS ϖ⁻¹ ∈ H := hS _ fun y hy => by
    have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hp, mul_one]
    exact hmax y hy
  have hD : nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (hball _ hϖ1.le)
      (H.mul_mem (H.mul_mem (H.inv_mem hw) hinv) hw)) (hball _ hϖ1.le)) (H.inv_mem hw)
  have hstep : ∀ t, nS t ∈ H → nS (ϖ⁻¹ ^ 2 * t) ∈ H := fun t ht => by
    rw [← conj_step hϖ0 t]
    exact H.mul_mem (H.mul_mem (H.inv_mem hD) ht) hD
  have hpow : ∀ k : ℕ, ∀ t, nS t ∈ H → nS ((ϖ⁻¹ ^ 2) ^ k * t) ∈ H := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih => intro t ht; rw [pow_succ', mul_assoc]; exact hstep _ (ih t ht)
  have hall : ∀ x : F, nS x ∈ H := by
    intro x
    have hq : ‖ϖ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg ϖ]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity) hq
    have h1 : ‖(ϖ ^ 2) ^ k * x‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      rw [lt_div_iff₀ (by positivity)] at hk
      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (ϖ ^ 2)) k]
    have e : x = (ϖ⁻¹ ^ 2) ^ k * ((ϖ ^ 2) ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_pow, one_mul]
    rw [e]
    exact hpow k _ (hball _ h1)
  exact eq_top_of H hw hall
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.SgnBasis

theorem eta_mul_isUnit (K : UQ) (a : K.E) (u : K.O) (hu : IsUnit u) :
    K.eta (a * algebraMap K.O K.E u) = K.eta a := by
  have hv : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact (IsDiscreteValuationRing.maximalIdeal K.O).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hu)
  simp only [UQ.eta, val, map_mul, hv, mul_one]

private theorem eta_det_trace_matrix_eq_of_span_eq (K : UQ) (B : InvAlg K)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A)
    (m : Fin (Module.finrank K.E B.A) → B.A)
    (hm : Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) :
    K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  classical
  have hP0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • e j = m l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [← hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hQ0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • m j = e l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose P hP using hP0
  choose Q hQ using hQ0

  have hli : LinearIndependent K.O e :=
    e.linearIndependent.restrict_scalars fun a b h =>
      IsFractionRing.injective K.O K.E (by simpa [Algebra.smul_def] using h)

  have hsum : ∀ l, ∑ i, (∑ j, Q l j * P j i) • e i = e l := by
    intro l
    calc ∑ i, (∑ j, Q l j * P j i) • e i = ∑ j, Q l j • ∑ i, P j i • e i := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = e l := by simp only [hP, hQ]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext l i
    have key : ∑ i, ((Matrix.of Q * Matrix.of P) l i - (1 : Matrix _ _ K.O) l i) • e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, hsum, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ key i)
  have hunit : IsUnit (Matrix.of P).det := Matrix.isUnit_det_of_left_inverse hQP

  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) *
        (Matrix.of P).transpose.map (algebraMap K.O K.E) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [← hP l]

    simp only [Finset.mul_sum, mul_smul_comm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K.E (P l j), map_smul, smul_eq_mul, mul_comm]
  have hdet : ((Matrix.of P).transpose.map (algebraMap K.O K.E)).det =
      algebraMap K.O K.E (Matrix.of P).det := by
    rw [RingHom.map_det, ← Matrix.det_transpose]
    rfl
  rw [hmat, Matrix.det_mul, hdet]
  exact eta_mul_isUnit K _ _ hunit

theorem sgnLat_span_basis (K : UQ) (B : InvAlg K) (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    B.sgnLat (Submodule.span K.O (Set.range e)) =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  dsimp only [InvAlg.sgnLat]
  exact eta_det_trace_matrix_eq_of_span_eq K B e _
    (Classical.epsilon_spec (p := fun m : Fin (Module.finrank K.E B.A) → B.A =>
      Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) ⟨e, rfl⟩)

end GlobalTheory.UnitLemma.SgnBasis
end

section

open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Unram.exists_basis_antifixed (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ star (b 1) = - b 1 ∧ b 1 * b 1 = algebraMap F E d ∧ d ≠ 0 := by
  have : CharZero F := h.charZero
  have hsmul : ∀ (c : F) (z : E), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, h.star_fix, mul_comm]
  obtain ⟨y, hy⟩ := h.star_ne
  set u : E := y - star y with hu
  have hsu : star u = -u := by rw [hu, star_sub, star_star, neg_sub]
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have key : ∀ s t : F, star (s • (1 : E) + t • u) = s • 1 + t • u → t = 0 := by
    intro s t hst
    rw [star_add, hsmul, hsmul, star_one, hsu, smul_neg, add_right_inj] at hst
    have h2 : (2 : F) • (t • u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hst]
      exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact (smul_eq_zero.mp h2).resolve_right hu0
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := key s t (by rw [hst, star_zero])
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right one_ne_zero
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.finrank_eq]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  have hsum := b.sum_repr (u * u)
  rw [Fin.sum_univ_two, hb0, hb1] at hsum
  have hfix : star (b.repr (u * u) 0 • (1 : E) + b.repr (u * u) 1 • u) =
      b.repr (u * u) 0 • 1 + b.repr (u * u) 1 • u := by
    rw [hsum, star_mul, hsu, neg_mul_neg]
  have h1 := key _ _ hfix
  rw [h1, zero_smul, add_zero] at hsum
  refine ⟨b, b.repr (u * u) 0, hb0, by rw [hb1, hsu], ?_, ?_⟩
  · rw [hb1, Algebra.algebraMap_eq_smul_one]
    exact hsum.symm
  · intro hd
    rw [hd, zero_smul] at hsum
    exact mul_self_ne_zero.mpr hu0 hsum.symm

theorem quadratic_star_structure {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (d : K) (hb0 : b 0 = 1) (hs : star (b 1) = - b 1)
    (hd : b 1 * b 1 = algebraMap K L d) (hK : ∀ x : K, star (algebraMap K L x) = algebraMap K L x)
    (hdu : IsUnit d) (h2 : IsUnit (2 : K)) :
    Function.Injective (algebraMap K L) ∧ (∀ y : L, algebraMap K L (Algebra.norm K y) = y * star y) ∧
      (∀ y : L, algebraMap K L (Algebra.trace K L y) = y + star y) ∧
      (∀ y' : L, (∀ y : L, Algebra.trace K L (star y' * y) = 0) → y' = 0) := by
  have hrep0 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 0 = a := by
    intro a c; simp
  have hrep1 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 1 = c := by
    intro a c; simp
  have hexp : ∀ y : L, y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [Fin.sum_univ_two]
  have hsmul : ∀ (c : K) (z : L), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, hK, mul_comm]
  have hstar : ∀ y : L, star y = b.repr y 0 • b 0 + (-b.repr y 1) • b 1 := by
    intro y
    conv_lhs => rw [hexp y]
    rw [star_add, hsmul, hsmul, hb0, star_one, hs, smul_neg, neg_smul]
  have hmul : ∀ z : L, z * b 1 = (b.repr z 1 * d) • b 0 + b.repr z 0 • b 1 := by
    intro z
    conv_lhs => rw [hexp z]
    simp only [Algebra.smul_def, hb0, mul_one, map_mul, add_mul]
    linear_combination (algebraMap K L (b.repr z 1)) * hd
  have hc0 : ∀ z : L, b.repr (z * b 0) = b.repr z := by
    intro z; rw [hb0, mul_one]
  have htr : ∀ z : L, Algebra.trace K L z = b.repr z 0 + b.repr z 0 := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep1]
  have hmap : ∀ x : K, algebraMap K L x = x • b 0 := by
    intro x; rw [hb0, Algebra.algebraMap_eq_smul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hmap] at hx
    have := hrep0 x 0
    rw [zero_smul, add_zero, hx] at this
    simp at this
    exact this.symm
  · intro y
    rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep0, hrep1]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) * (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [Algebra.smul_def, hb0, mul_one, map_mul, map_sub, map_neg]
          linear_combination (algebraMap K L (b.repr y 1) * algebraMap K L (b.repr y 1)) * hd
      _ = y * star y := by rw [← hexp y, ← hstar y]
  · intro y
    rw [htr, hmap]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) + (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [add_smul, neg_smul]; abel
      _ = y + star y := by rw [← hexp y, ← hstar y]
  · intro y' hy'
    have g1 := hy' 1
    have g2 := hy' (b 1)
    rw [mul_one, htr, hstar, hrep0] at g1
    rw [hmul, htr, hrep0, hstar, hrep1] at g2
    have hp : b.repr y' 0 = 0 := by
      have h3 : (2 : K) * b.repr y' 0 = 0 := by rw [two_mul]; exact g1
      exact h2.mul_right_eq_zero.mp h3
    have hq : b.repr y' 1 = 0 := by
      have h3 : (2 : K) * (b.repr y' 1 * d) = 0 := by linear_combination -g2
      exact hdu.mul_left_eq_zero.mp (h2.mul_right_eq_zero.mp h3)
    rw [hexp y', hp, hq, zero_smul, zero_smul, add_zero]

theorem Et.quadratic_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nonempty (Module.Basis (Fin 2) A.K A.L) ∧ Function.Injective (algebraMap A.K A.L) ∧ (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (∀ y' : A.L, (∀ y : A.L, Algebra.trace A.K A.L (star y' * y) = 0) → y' = 0) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  let B : Module.Basis (Fin 2) A.K A.L := A.push.symm.out.basis b
  have hB : ∀ i, B i = algebraMap E A.L (b i) := fun i => by
    simp [B, IsBaseChange.basis_apply]
  have key := quadratic_star_structure B (algebraMap F A.K d) (by rw [hB, hb0, map_one])
    (by rw [hB, A.star_E, hs, map_neg])
    (by
      rw [hB, ← map_mul, hd, ← IsScalarTower.algebraMap_apply F E A.L,
        ← IsScalarTower.algebraMap_apply F A.K A.L])
    A.star_K ((isUnit_iff_ne_zero.mpr hd0).map _)
    (by
      have h2F := (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : F) ≠ 0)).map (algebraMap F A.K)
      rwa [map_ofNat] at h2F)
  exact ⟨⟨B⟩, key.1, key.2.1, key.2.2.1, key.2.2.2⟩

end GlobalTheory.JR
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem et_equiv_continuous (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous j ∧ Continuous j.symm := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : CompleteSpace F := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace F
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : FiniteDimensional F (Fin r → E) := inferInstance
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  refine ⟨?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap (R := F) (j.toLinearMap.restrictScalars F)
  · exact LinearMap.continuous_of_finiteDimensional (j.symm.toLinearMap.restrictScalars F)

end GlobalTheory.JR
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilRing_eq_integral_add_eisensteinFiltration : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), j < l → ∀ f ∈ S O K e, ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := by
  first | exact @GlobalTheory.BK.SDec.S_eq_A_add_Fil | exact GlobalTheory.BK.SDec.S_eq_A_add_Fil | (intros; apply GlobalTheory.BK.SDec.S_eq_A_add_Fil <;> assumption)
end
