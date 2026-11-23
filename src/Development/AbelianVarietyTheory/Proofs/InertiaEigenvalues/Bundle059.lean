module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open GlobalTheory.JR Matrix

noncomputable section

namespace GlobalTheory.JR.GLift

theorem norm_mul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : Fin n) :
    ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem norm_one_apply_le_one {F : Type} [NormedField F] {n : ℕ} (i j : Fin n) :
    ‖(1 : Matrix (Fin n) (Fin n) F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

def glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] : Subgroup (GL (Fin n) F) where
  carrier := glO n F
  mul_mem' {a b} ha hb := by
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp only [inv_one, Units.val_one]
    exact ⟨norm_one_apply_le_one i j, norm_one_apply_le_one i j⟩
  inv_mem' {a} ha := by
    intro i j
    rw [inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩

theorem coe_glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] :
    (glOSub n F : Set (GL (Fin n) F)) = glO n F := rfl

end GlobalTheory.JR.GLift
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbitProper

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem companionMatrixOfCoeffs_pow_mulVec_first_basis (p : Fin r → k) (n : ℕ) (hn : n < r) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = Pi.single (⟨n, hn⟩ : Fin r) 1 := by
  induction n with
  | zero =>
    rw [pow_zero, one_mulVec]
    funext i
    simp [Pi.single_apply, Fin.ext_iff]
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), mulVec_single_one]
    funext i
    simp only [companion, transpose_apply, of_apply, Pi.single_apply, Fin.ext_iff]
    have : ¬ (n + 1 = r) := by omega
    simp [this]

theorem conj_pow_GL (g : GL (Fin r) k) (A : Matrix (Fin r) (Fin r) k) (j : ℕ) :
    ((g : Matrix (Fin r) (Fin r) k) * A * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)) ^ j =
      (g : Matrix (Fin r) (Fin r) k) * A ^ j * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  exact Units.conj_pow g A j

theorem Bm_sec (a : Inv r k) : Bm (sec a) = 1 := by
  ext i j
  simp only [Bm, sec, of_apply]
  rw [companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2]
  simp [Pi.single_apply, Matrix.one_apply]

theorem Bm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  ext i j
  simp only [Bm, act, of_apply]
  rw [conj_pow_GL, mulVec_mulVec, mul_assoc _ _ (g : Matrix (Fin r) (Fin r) k), Units.inv_mul, mul_one,
    ← mulVec_mulVec]
  simp [Matrix.mul_apply, mulVec, dotProduct]

theorem Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, of_apply]
  rw [conj_pow_GL, vecMul_vecMul, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← vecMul_vecMul]
  simp [Matrix.mul_apply, vecMul, dotProduct]

theorem Cm_sec (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, sec, of_apply]
  rw [pow_add, ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2, mulVec_single_one, dotProduct_comm]
  simp [vecMul, dotProduct, transpose_apply, mul_comm]

end Alg

section Top
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_companion : Continuous (fun p : Fin r → F => companion p) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [companion, of_apply]
  split_ifs
  · exact ((continuous_apply i)).neg
  all_goals exact continuous_const

theorem cont_sec : Continuous (fun a : Inv r F => sec a) := by
  unfold sec
  exact (cont_companion.comp continuous_fst).prodMk
    (continuous_const.prodMk ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))

theorem cont_act : Continuous (fun p : GL (Fin r) F × Gl r F => act p.1 p.2) := by
  have h1 : Continuous (fun p : GL (Fin r) F × Gl r F => ((p.1 : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun p : GL (Fin r) F × Gl r F => (((p.1)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
    Units.continuous_coe_inv.comp continuous_fst
  unfold act
  exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
    ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

theorem cont_charpoly_coeff (i : ℕ) :
    Continuous (fun A : Matrix (Fin r) (Fin r) F => A.charpoly.coeff i) := by
  have h : ∀ A : Matrix (Fin r) (Fin r) F, A.charpoly.coeff i =
      MvPolynomial.eval (fun ij : Fin r × Fin r => A ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom F) ((Matrix.charpoly.univ ℤ (Fin r)).coeff i)) := by
    intro A
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  simp_rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem cont_mom (n : ℕ) : Continuous (fun Y : Gl r F => mom Y n) := by
  unfold mom
  exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).dotProduct
    (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow n).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem cont_inv : Continuous (fun Y : Gl r F => inv Y) := by
  unfold inv
  exact (continuous_pi fun i : Fin r => (cont_charpoly_coeff (r := r) (F := F) (i : ℕ)).comp continuous_fst).prodMk
    ((continuous_pi fun i : Fin r => cont_mom (r := r) (F := F) (i : ℕ)).prodMk
      (show Continuous fun Y : Gl r F => Y.2.2.2 from continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem cont_hankel : Continuous (fun a : Inv r F => hankel a) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Inv r F => mom (sec a) ((i : ℕ) + (j : ℕ))
    exact (cont_mom _).comp cont_sec

theorem cont_Delta : Continuous (fun a : Inv r F => Delta a) := cont_hankel.matrix_det

end Top

section Cpt
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_Bm : Continuous (fun Y : Gl r F => Bm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => ((Y.1 ^ (j : ℕ)) *ᵥ Y.2.1) i
    exact (continuous_apply i).comp
      (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _).matrix_mulVec
        (continuous_fst.comp continuous_snd))

theorem cont_Cm : Continuous (fun Y : Gl r F => Cm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => (Y.2.2.1 ᵥ* (Y.1 ^ (i : ℕ))) j
    exact (continuous_apply j).comp
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).matrix_vecMul
        ((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _))

theorem contAt_hankel_inv (a : Inv r F) (ha : Delta a ≠ 0) :
    ContinuousAt (fun b : Inv r F => (hankel b)⁻¹) a := by
  refine (continuousAt_matrix_inv _ ?_).comp cont_hankel.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ha

theorem coe_eq (g : GL (Fin r) F) (a : Inv r F) :
    (g : Matrix (Fin r) (Fin r) F) = Bm (act g (sec a)) := by
  rw [Bm_act, Bm_sec, mul_one]

theorem coe_inv_eq (g : GL (Fin r) F) (a : Inv r F) (ha : Delta a ≠ 0) :
    ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = (hankel a)⁻¹ * Cm (act g (sec a)) := by
  have h : IsUnit (hankel a).det := isUnit_iff_ne_zero.mpr ha
  rw [Cm_act, Cm_sec, ← mul_assoc, nonsing_inv_mul _ h, one_mul]

theorem isCompact_set (C : Set (Gl r F)) (Ω : Set (Inv r F)) (hC : IsCompact C) (hΩ : IsCompact Ω)
    (hD : ∀ a ∈ Ω, Delta a ≠ 0) :
    IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  set Φ : Gl r F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    fun q => ((Bm q.1, MulOpposite.op ((hankel q.2)⁻¹ * Cm q.1)), q.2) with hΦdef
  have hΦ : ContinuousOn Φ (C ×ˢ Ω) := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    have h3 : ContinuousAt (fun q : Gl r F × Inv r F => (hankel q.2)⁻¹) q :=
      (contAt_hankel_inv q.2 (hD q.2 hq.2)).comp continuous_snd.continuousAt
    exact (((cont_Bm.comp continuous_fst).continuousAt).prodMk
      (MulOpposite.continuous_op.continuousAt.comp (h3.mul (cont_Cm.comp continuous_fst).continuousAt))).prodMk
      continuous_snd.continuousAt
  set e : GL (Fin r) F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    Prod.map (Units.embedProduct (Matrix (Fin r) (Fin r) F)) id with hedef
  have he : Topology.IsClosedEmbedding e :=
    Units.isClosedEmbedding_embedProduct.prodMap Topology.IsClosedEmbedding.id
  have hK : IsCompact (e ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    he.isCompact_preimage ((hC.prod hΩ).image_of_continuousOn hΦ)
  have hS : IsClosed {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
    have hc : Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) :=
      cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd))
    exact (hΩ.isClosed.preimage continuous_snd).inter (hC.isClosed.preimage hc)
  refine hK.of_isClosed_subset hS ?_
  rintro ⟨g, a⟩ ⟨ha, hY⟩
  refine ⟨(act g (sec a), a), ⟨hY, ha⟩, ?_⟩
  simp only [hΦdef, hedef, Prod.map, id, Units.embedProduct_apply]
  rw [← coe_eq g a, ← coe_inv_eq g a (hD a ha)]

end Cpt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) ∧ Continuous (fun Y : Gl r F => inv Y) ∧ Continuous (fun a : Inv r F => Delta a) ∧ ∀ (C : Set (Gl r F)) (Ω : Set (Inv r F)), IsCompact C → IsCompact Ω → (∀ a ∈ Ω, Delta a ≠ 0) → IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  intro F E _ _ _ _ _ r
  exact ⟨cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd)), cont_inv, cont_Delta,
    fun C Ω hC hΩ hD => isCompact_set C Ω hC hΩ hD⟩

end GlobalTheory.JR.OrbitProper
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TraceUnit

section Ultra
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max_of_ultra (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem norm_sq_sub_sq_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x ^ 2 - y ^ 2‖ ≤ ‖x - y‖ := by
  have h1 : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [h1, norm_mul]
  have h2 : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  calc ‖x - y‖ * ‖x + y‖ ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖x - y‖ := mul_one _

theorem norm_pow_two_pow_sub_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ) :
    ‖x ^ 2 ^ k - y ^ 2 ^ k‖ ≤ ‖x - y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2 ^ k) ^ 2 := fun z => by rw [pow_succ, pow_mul]
    rw [e, e]
    exact (norm_sq_sub_sq_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy)).trans ih

theorem norm_sub_lt_one_of_sq {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (h : ‖x ^ 2 - y ^ 2‖ < 1) : ‖x - y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hle : ‖x - y‖ ≤ 1 := (norm_sub_le_max_of_ultra x y).trans (max_le hx hy)
  have heq : ‖x - y‖ = 1 := le_antisymm hle hc
  have e : x ^ 2 - y ^ 2 = (x - y) ^ 2 + 2 * y * (x - y) := by ring
  have hA : ‖(x - y) ^ 2‖ = 1 := by rw [norm_pow, heq, one_pow]
  have hB : ‖2 * y * (x - y)‖ < 1 := by
    rw [norm_mul, norm_mul, heq, mul_one]
    calc ‖(2 : K)‖ * ‖y‖ ≤ ‖(2 : K)‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h2
  have h3 : ‖(x - y) ^ 2 + 2 * y * (x - y)‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hA]; exact hB.ne'), hA]
    exact max_eq_left hB.le
  rw [e, h3] at h
  exact lt_irrefl _ h

theorem norm_sub_lt_one_of_pow {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ)
    (h : ‖x ^ 2 ^ k - y ^ 2 ^ k‖ < 1) : ‖x - y‖ < 1 := by
  induction k generalizing x y with
  | zero => simpa using h
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2) ^ 2 ^ k := fun z => by rw [pow_succ', pow_mul]
    rw [e, e] at h
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hy2 : ‖y ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    exact norm_sub_lt_one_of_sq h2 hx hy (ih hx2 hy2 h)

theorem exists_pow_close [ProperSpace K] {w : K} (hw : ‖w‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ ‖w ^ 2 ^ i - w ^ 2 ^ j‖ < 1 := by
  have hmem : ∀ n : ℕ, w ^ 2 ^ n ∈ Metric.closedBall (0 : K) 1 := fun n => by
    rw [mem_closedBall_zero_iff, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : K) 1).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (1 / 2) (by norm_num)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 : dist (w ^ 2 ^ φ N) a < 1 / 2 := hN N le_rfl
  have h2 : dist (w ^ 2 ^ φ (N + 1)) a < 1 / 2 := hN (N + 1) (Nat.le_succ N)
  rw [← dist_eq_norm]
  calc dist (w ^ 2 ^ φ N) (w ^ 2 ^ φ (N + 1)) ≤ dist (w ^ 2 ^ φ N) a + dist a (w ^ 2 ^ φ (N + 1)) :=
        dist_triangle _ _ _
    _ < 1 / 2 + 1 / 2 := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = 1 := by norm_num

end Ultra

theorem exists_trace_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E],
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
      ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by
  intro F E _ _ _ _ hU htr
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : CharZero F := hU.charZero
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  have h20 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have h2le : ‖(2 : E)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one E 2
    simpa using this
  rcases h2le.lt_or_eq with h2 | h2
  swap
  ·
    refine ⟨2⁻¹, by rw [norm_inv, h2, inv_one], ?_⟩
    have hs : star (2⁻¹ : E) = 2⁻¹ := by
      have : (2⁻¹ : E) = algebraMap F E 2⁻¹ := by rw [map_inv₀, map_ofNat]
      rw [this, hU.star_fix]
    rw [← norm_algebraMap' E, htr, hs, ← two_mul, mul_inv_cancel₀ h20, norm_one]

  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ a : F, y - algebraMap F E a ≠ 0 := fun a h => hy (by rw [sub_eq_zero.1 h, hU.star_fix])
  have hcont : Continuous fun a : F => ‖y - algebraMap F E a‖ := by fun_prop
  obtain ⟨x, -, hx⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    (Metric.nonempty_closedBall.2 (norm_nonneg _)) hcont.continuousOn
  have hmin : ∀ a : F, ‖y - algebraMap F E x‖ ≤ ‖y - algebraMap F E a‖ := by
    intro a
    have h0 : ‖y - algebraMap F E x‖ ≤ ‖y‖ := by
      have := isMinOn_iff.1 hx 0 (Metric.mem_closedBall_self (norm_nonneg y))
      simpa using this
    by_cases ha : ‖a‖ ≤ ‖y‖
    · exact isMinOn_iff.1 hx a (mem_closedBall_zero_iff.2 ha)
    · push_neg at ha
      have hm : ‖a‖ ≤ max ‖y‖ ‖y - algebraMap F E a‖ := by
        have := norm_sub_le_max_of_ultra y (y - algebraMap F E a)
        rwa [sub_sub_cancel, norm_algebraMap'] at this
      rcases le_max_iff.1 hm with h | h <;> linarith
  obtain ⟨t, ht⟩ := hU.unram (y - algebraMap F E x)
  have hd : 0 < ‖y - algebraMap F E x‖ := norm_pos_iff.2 (hyF x)
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [← norm_algebraMap' E t, h0, norm_zero] at ht
    linarith
  set u := (y - algebraMap F E x) * (algebraMap F E t)⁻¹ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_inv, norm_algebraMap', ← ht, mul_inv_cancel₀ hd.ne']
  have hfar : ∀ a : F, 1 ≤ ‖u - algebraMap F E a‖ := by
    intro a
    have e : u - algebraMap F E a = (y - algebraMap F E (x + t * a)) * (algebraMap F E t)⁻¹ := by
      rw [hu, map_add (f := _), map_mul]
      field_simp
      ring
    rw [e, norm_mul, norm_inv, norm_algebraMap', ← ht, le_mul_inv_iff₀ hd, one_mul]
    exact hmin _
  refine ⟨u, hu1.le, ?_⟩
  have hle : ‖Algebra.trace F E u‖ ≤ 1 := by
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu1.le (by rw [hU.norm_star]; exact hu1.le))
  refine le_antisymm hle (not_lt.1 fun hs => ?_)

  set n := u * star u with hn
  have hnn : star n = n := by rw [hn, star_mul, star_star, mul_comm]
  set v : F := -(Algebra.trace F E n / 2) with hvd
  have hv : algebraMap F E v = -n := by
    rw [hvd, map_neg, map_div₀, htr, hnn, map_ofNat]
    field_simp
    ring
  have hvn : ‖algebraMap F E v‖ ≤ 1 := by
    rw [hv, norm_neg, hn, norm_mul, hU.norm_star, hu1, one_mul]
  have hq : ‖u ^ 2 - algebraMap F E v‖ < 1 := by
    have e : u ^ 2 - algebraMap F E v = algebraMap F E (Algebra.trace F E u) * u := by
      rw [hv, htr, hn]; ring
    rw [e, norm_mul, norm_algebraMap', hu1, mul_one]
    exact hs
  obtain ⟨i, j, hij, hc⟩ := exists_pow_close hu1.le
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  have e1 : u ^ 2 ^ (i + (m + 1)) = (u ^ 2 ^ (m + 1)) ^ 2 ^ i := by
    rw [← pow_mul, ← pow_add, Nat.add_comm (m + 1) i]
  rw [e1] at hc
  have hpow1 : ‖u ^ 2 ^ (m + 1)‖ ≤ 1 := by rw [norm_pow, hu1, one_pow]
  have hA : ‖u - u ^ 2 ^ (m + 1)‖ < 1 := norm_sub_lt_one_of_pow h2 hu1.le hpow1 i hc
  have e2 : u ^ 2 ^ (m + 1) = (u ^ 2) ^ 2 ^ m := by rw [pow_succ', pow_mul]
  have hB : ‖(u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m‖ < 1 :=
    (norm_pow_two_pow_sub_le (by rw [norm_pow, hu1, one_pow]) hvn m).trans_lt hq
  have hC : ‖u - algebraMap F E (v ^ 2 ^ m)‖ < 1 := by
    rw [map_pow]
    have e3 : u - (algebraMap F E v) ^ 2 ^ m =
        (u - u ^ 2 ^ (m + 1)) + ((u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m) := by
      rw [e2]; ring
    rw [e3]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hA hB)
  linarith [hfar (v ^ 2 ^ m)]

end GlobalTheory.TraceUnit
end

section

namespace GlobalTheory.UnitLemma.Witt

open GlobalTheory.UnitLemma Polynomial

theorem exists_conj (K : UQ) : ∃ s : K.O →+* K.O,
    ∀ x, algebraMap K.O K.E (s x) = K.c (algebraMap K.O K.E x) := by
  choose f hf using K.c_int
  have inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [← hf]; simp)
            map_mul' := fun x y => inj (by rw [map_mul, ← hf, ← hf, ← hf]; simp)
            map_zero' := inj (by rw [← hf]; simp)
            map_add' := fun x y => inj (by rw [map_add (f := _), ← hf, ← hf, ← hf]; simp) }, fun x => (hf x).symm⟩

end GlobalTheory.UnitLemma.Witt
end
