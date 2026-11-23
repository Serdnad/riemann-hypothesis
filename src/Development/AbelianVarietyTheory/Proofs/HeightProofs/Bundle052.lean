module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle224
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KGap

theorem entry_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖Y i j‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs
  calc ‖Y i j‖ ^ 2 ≤ ∑ j', ‖Y i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖Y i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖Y i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖Y i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

theorem hs_nonneg' {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs; positivity

theorem sup_norm_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  have h : ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ≤ Real.sqrt (Formalism.REAL.hs Y) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    exact Real.le_sqrt_of_sq_le (entry_sq_le_hs Y i j)
  calc ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Real.sqrt (Formalism.REAL.hs Y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Formalism.REAL.hs Y := Real.sq_sqrt (hs_nonneg' Y)

theorem spanning_coef_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ C : ℝ, 0 ≤ C ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y := by
  intro n ε r X hX
  let Tm : (Fin r → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun c => Matrix.of.symm (∑ j, (c j : ℂ) • X j)
      map_add' := by
        intro a b; funext i k
        simp [add_smul, Finset.sum_add_distrib, Matrix.sum_apply]
      map_smul' := by
        intro t a; funext i k
        simp [Matrix.sum_apply, Finset.mul_sum, mul_assoc] }
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Tm.rangeRestrict (LinearMap.range_rangeRestrict Tm)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range Tm).subtype (Submodule.ker_subtype _)
  let L : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin r → ℝ) := g ∘ₗ P
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨r * ‖Lc‖ ^ 2, by positivity, ?_⟩
  intro Y hY
  obtain ⟨c0, hc0⟩ := hX Y hY
  have hYW : Matrix.of.symm Y ∈ LinearMap.range Tm := ⟨c0, by simp [Tm, hc0]⟩
  have hPY : P (Matrix.of.symm Y) = ⟨_, hYW⟩ := by
    have := LinearMap.congr_fun hP ⟨_, hYW⟩
    simpa using this
  refine ⟨L (Matrix.of.symm Y), ?_, ?_⟩
  · have h1 := LinearMap.congr_fun hg (P (Matrix.of.symm Y))
    have h2 : Tm (L (Matrix.of.symm Y)) = Matrix.of.symm Y := by
      have := congrArg Subtype.val h1
      change Tm (g (P (Matrix.of.symm Y))) = _ at this
      change Tm (g (P (Matrix.of.symm Y))) = _
      rw [hPY] at this ⊢
      exact this
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa [Tm, Matrix.sum_apply] using h3.symm
  · set v := Matrix.of.symm Y with hv
    have hb : ∀ j, (L v) j ^ 2 ≤ ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by
      intro j
      have h1 : ‖(L v) j‖ ≤ ‖L v‖ := norm_le_pi_norm (L v) j
      have h2 : ‖L v‖ ≤ ‖Lc‖ * ‖v‖ := Lc.le_opNorm v
      have h3 : |(L v) j| ≤ ‖Lc‖ * ‖v‖ := by
        rw [← Real.norm_eq_abs]; exact h1.trans h2
      rw [← mul_pow]
      exact sq_le_sq' (by linarith [abs_le.mp h3]) (abs_le.mp h3).2
    have hv2 : ‖v‖ ^ 2 ≤ Formalism.REAL.hs Y := sup_norm_sq_le_hs Y
    calc ∑ j, (L v) j ^ 2 ≤ ∑ _j : Fin r, ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := Finset.sum_le_sum fun j _ => hb j
      _ = r * ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by simp; ring
      _ ≤ r * ‖Lc‖ ^ 2 * Formalism.REAL.hs Y := by gcongr

end GlobalTheory.KGap
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KSpan

def kSub {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | inK ε Y}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · unfold inG at *
      rw [conjTranspose_add, add_mul, mul_add]
      calc _ = (aᴴ * Jm ε + Jm ε * a) + (bᴴ * Jm ε + Jm ε * b) := by abel
        _ = 0 := by rw [ha1, hb1, add_zero]
    · rw [add_mul, mul_add, ha2, hb2]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · simp [inG]
    · simp
  smul_mem' := by
    intro t Z hZ
    have h := inK_smul_real ε hZ t
    rwa [Complex.coe_smul] at h

theorem finite_real_span : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  intro n ε
  let b := Module.finBasis ℝ (kSub ε)
  refine ⟨Module.finrank ℝ (kSub ε), fun j => ((b j : kSub ε) : Matrix (Fin n) (Fin n) ℂ), fun j => (b j).2, ?_⟩
  intro Y hY
  refine ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩
  have h2 := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.coe_smul]

end GlobalTheory.KSpan
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem FamGrowth.bdd_of_isCompact {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hG : FamGrowth ε N F)
    {w : List (Mx n)} (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {K : Set (Mx n)} (hK : IsCompact K) (hKU : K ⊆ UJset ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ‖F w y‖ ≤ B := by
  obtain ⟨C, hC⟩ := hG w hw
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_hs.continuousOn
  refine ⟨|C| * (1 + max M 0) ^ N, by positivity, fun y hy => ?_⟩
  have h1 : hs y ≤ max M 0 := (hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  have h0 : 0 ≤ hs y := hs_nonneg y
  calc ‖F w y‖ ≤ C * (1 + hs y) ^ N := hC y (hKU hy)
    _ ≤ |C| * (1 + hs y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (1 + max M 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (abs_nonneg C)

noncomputable def expSweep (K : Set (Mx n)) (X : Mx n) : Set (Mx n) :=
  (fun p : Mx n × ℝ => p.1 * NormedSpace.exp (p.2 • X)) '' (K ×ˢ Set.Icc (-1 : ℝ) 1)

theorem isCompact_expSweep {K : Set (Mx n)} (hK : IsCompact K) (X : Mx n) : IsCompact (expSweep K X) :=
  (hK.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).image
    (continuous_fst.matrix_mul ((continuous_exp_smul X).comp continuous_snd))
theorem expSweep_sub {K : Set (Mx n)} (hKU : K ⊆ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    expSweep K X ⊆ UJset ε := by
  rintro _ ⟨⟨z, s⟩, ⟨hz, -⟩, rfl⟩
  exact mul_mem_UJ (hKU hz) (exp_mem_UJ hX s)

theorem mem_expSweep {K : Set (Mx n)} {z : Mx n} (hz : z ∈ K) (X : Mx n) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    z * NormedSpace.exp (s • X) ∈ expSweep K X := ⟨(z, s), ⟨hz, hs⟩, rfl⟩

theorem exp_zero_smul_mx (X : Mx n) : NormedSpace.exp ((0 : ℝ) • X) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

theorem IsDerFam.norm_sub_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z‖ ≤ B * |t| := by
  have h := norm_sub_le_of_deriv_Icc (f := fun s => F w (z * NormedSpace.exp (s • X)))
    (fun s => hF.hasDerivAt_exp hw hX hz s) zero_le_one hB (t := t) (abs_le.1 ht)
  simpa only [exp_zero_smul_mx, Matrix.mul_one] using h

theorem IsDerFam.norm_taylor_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z‖ ≤ B * t ^ 2 := by
  have hXw : ∀ Y ∈ X :: w, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    exacts [hX, hw Y hY]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)
  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|,
      ‖F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z‖ ≤ B * |t| := by
    intro s hs
    have hs1 : |s| ≤ |t| := abs_le.2 hs
    exact (hF.norm_sub_exp_le hXw hX hz hB (hs1.trans ht)).trans (mul_le_mul_of_nonneg_left hs1 hB0)
  have hd : ∀ s, HasDerivAt (fun s : ℝ => F w (z * NormedSpace.exp (s • X)) - s • F (X :: w) z)
      (F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z) s := by
    intro s
    have := (hF.hasDerivAt_exp hw hX hz s).fun_sub ((hasDerivAt_id s).smul_const (F (X :: w) z))
    simpa only [id, one_smul] using this
  have h := norm_sub_le_of_deriv_Icc hd (abs_nonneg t) h1 (t := t) ⟨neg_abs_le t, le_abs_self t⟩
  simp only [exp_zero_smul_mx, Matrix.mul_one, zero_smul, sub_zero, NormedSpace.exp_zero] at h
  have e : F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z =
      F w (z * NormedSpace.exp (t • X)) - t • F (X :: w) z - F w z := by abel
  rw [e]
  calc _ ≤ B * |t| * |t| := h
    _ = B * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem lie_cons {Y : Mx n} {w : List (Mx n)} (hY : Y ∈ lieSet ε) (hw : ∀ Z ∈ w, Z ∈ lieSet ε) :
    ∀ Z ∈ Y :: w, Z ∈ lieSet ε := by
  intro Z hZ
  rcases List.mem_cons.1 hZ with rfl | hZ
  exacts [hY, hw Z hZ]

theorem IsDerFam.taylor_prod {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) (hG : FamGrowth ε N F)
    {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) : ∀ (d : ℕ) (b : Fin d → Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ K : Set (Mx n), IsCompact K → K ⊆ UJset ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ t : Fin d → ℝ, ‖t‖ ≤ 1 →
      ‖F l (z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod) - F l z - ∑ i, t i • F (b i :: l) z‖ ≤
        C * ‖t‖ ^ 2 := by
  intro d
  induction d with
  | zero =>
    intro b hb K hK hKU
    refine ⟨0, le_rfl, fun z _ t _ => ?_⟩
    simp
  | succ d ih =>
    intro b hb K hK hKU
    have hX := hb 0
    have hK' := isCompact_expSweep hK (b 0)
    have hK'U := expSweep_sub hKU hX
    obtain ⟨C', hC'0, hC'⟩ := ih (fun i => b i.succ) (fun i => hb _) _ hK' hK'U
    obtain ⟨B0, hB00, hB0⟩ := hG.bdd_of_isCompact (lie_cons hX (lie_cons hX hl)) hK' hK'U
    have hBi : ∀ i : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ expSweep K (b 0), ‖F (b 0 :: b i.succ :: l) y‖ ≤ B :=
      fun i => hG.bdd_of_isCompact (lie_cons hX (lie_cons (hb _) hl)) hK' hK'U
    choose B hBnn hB using hBi
    have hBs : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hBnn i
    refine ⟨C' + ∑ i, B i + B0, by positivity, fun z hz t ht => ?_⟩
    have hzU := hKU hz
    have hti : ∀ i, |t i| ≤ ‖t‖ := fun i => by simpa using norm_le_pi_norm t i
    have ht0 : t 0 ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 ((hti 0).trans ht)
    have ht' : ‖(fun i : Fin d => t i.succ)‖ ≤ ‖t‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun i => norm_le_pi_norm t i.succ
    have hz1 := mem_expSweep hz (b 0) ht0
    have hprod : z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod =
        z * NormedSpace.exp (t 0 • b 0) * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod := by
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_assoc]
    rw [hprod, Fin.sum_univ_succ]
    set z1 := z * NormedSpace.exp (t 0 • b 0) with hz1def
    have h1 := hC' z1 hz1 (fun i => t i.succ) (ht'.trans ht)
    have h2 : ‖∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z)‖ ≤ (∑ i, B i) * ‖t‖ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      have hd := hF.norm_sub_exp_le (lie_cons (hb i.succ) hl) hX hzU
        (fun s hs => hB i _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
      calc |t i.succ| * ‖F (b i.succ :: l) z1 - F (b i.succ :: l) z‖ ≤ ‖t‖ * (B i * ‖t‖) :=
            mul_le_mul (hti _) (hd.trans (mul_le_mul_of_nonneg_left (hti 0) (hBnn i))) (norm_nonneg _)
              (norm_nonneg _)
        _ = B i * ‖t‖ ^ 2 := by ring
    have h3 := hF.norm_taylor_exp_le hl hX hzU (fun s hs => hB0 _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
    have h3' : B0 * t 0 ^ 2 ≤ B0 * ‖t‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hB00
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hti 0) 2
    have h1' : C' * ‖(fun i : Fin d => t i.succ)‖ ^ 2 ≤ C' * ‖t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) hC'0
    have e : F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z -
        (t 0 • F (b 0 :: l) z + ∑ i : Fin d, t i.succ • F (b i.succ :: l) z) =
        (F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z1 -
          ∑ i : Fin d, t i.succ • F (b i.succ :: l) z1) +
        ∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z) +
        (F l z1 - F l z - t 0 • F (b 0 :: l) z) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    have : (C' + ∑ i, B i + B0) * ‖t‖ ^ 2 = C' * ‖t‖ ^ 2 + (∑ i, B i) * ‖t‖ ^ 2 + B0 * ‖t‖ ^ 2 := by ring
    rw [this]
    exact add_le_add_three (h1.trans h1') h2 (h3.trans h3')

theorem hasFDerivAt_derFam_prodExp : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  intro n ε N F hF hG l hl d b hb g hg
  obtain ⟨C, -, hC⟩ := hF.taylor_prod hG hl d b hb {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e0 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • b i)).prod = 1 := by
    simp [List.prod_ofFn]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh
  rw [mem_closedBall_zero_iff] at hh
  simp only [zero_add, e0, Matrix.mul_one, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_pow, norm_norm]
  exact hC g rfl h hh

end GlobalTheory.TypeSum
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section
namespace GlobalTheory.KFinApprox

theorem approx_identity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ),
    (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ →
    ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  intro n ε X _ F hF C hC δ hδ

  have hFx : ∀ x, Continuous (F x) := fun x =>
    hF.comp (Continuous.prodMk continuous_const continuous_id)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact
  have hintR : ∀ g : KG ε → ℝ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

  have hG : Continuous fun z : KG ε × X => ‖F z.2 z.1 - F z.2 1‖ :=
    ((hF.comp (Continuous.prodMk continuous_snd continuous_fst)).sub
      (hF.comp (Continuous.prodMk continuous_snd continuous_const))).norm
  have hev : ∀ᶠ k in 𝓝 (1 : KG ε), ∀ x ∈ C, ‖F x k - F x 1‖ < δ / 3 := by
    refine hC.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have ht := hG.tendsto ((1 : KG ε), y)
    simp only [sub_self, norm_zero] at ht
    exact ht.eventually_lt_const (by positivity)
  obtain ⟨U, hUP, hUo, hU1⟩ := eventually_nhds_iff.1 hev

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hUo.isClosed_compl
    (isClosed_singleton (x := (1 : KG ε))) (Set.disjoint_singleton_right.2 (fun h => h hU1))
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : KG ε))
  have hfnn : ∀ k, 0 ≤ f k := fun k => (hf01 k).1
  have hfU : ∀ k, k ∉ U → f k = 0 := fun k hk => by simpa using hf0 hk
  have hIpos : 0 < ∫ k, f k ∂(muK ε) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous
      (isClosed_tsupport _).isCompact (fun k => hfnn k) (x := 1) (by rw [hf1']; norm_num)
  obtain ⟨I, hIdef⟩ : ∃ I, ∫ k, f k ∂(muK ε) = I := ⟨_, rfl⟩
  rw [hIdef] at hIpos

  let ψ : C(KG ε, ℂ) := ⟨fun k => ((f k / I : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (f.continuous.div_const I)⟩
  have hψ : ∀ k, ψ k = ((f k / I : ℝ) : ℂ) := fun k => rfl
  have hψint : ∫ k, ψ k ∂(muK ε) = 1 := by
    simp only [hψ]
    rw [integral_complex_ofReal, integral_div, hIdef, div_self hIpos.ne']
    simp
  have hψnorm : ∀ k, ‖ψ k‖ = f k / I := fun k => by
    rw [hψ, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hfnn k) hIpos.le)]
  have h7 := GlobalTheory.KFinSep.finAlg_dense ε

  obtain ⟨M, hM⟩ := (hC.prod isCompact_univ).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨A, hA, hMA⟩ : ∃ A : ℝ, 0 < A ∧ M * (muK ε).real Set.univ ≤ A := by
    have hm : 0 ≤ (muK ε).real Set.univ := measureReal_nonneg
    refine ⟨(|M| + 1) * ((muK ε).real Set.univ + 1), by positivity, ?_⟩
    nlinarith [le_abs_self M, abs_nonneg M]
  have hη : 0 < δ / (3 * A) := div_pos hδ (by linarith)

  have hmem : ψ ∈ (GlobalTheory.KFinSep.finAlg ε).topologicalClosure := by
    rw [h7]; exact StarSubalgebra.mem_top
  have hmem' : ψ ∈ closure ((GlobalTheory.KFinSep.finAlg ε : Set C(KG ε, ℂ))) := hmem
  obtain ⟨p, hp, hpd⟩ := Metric.mem_closure_iff.1 hmem' (δ / (3 * A)) hη
  have hpK : KFinFun ε p := hp.1
  have hpk : ∀ k, ‖ψ k - p k‖ ≤ δ / (3 * A) := fun k => by
    have h := ContinuousMap.norm_coe_le_norm (ψ - p) k
    rw [← dist_eq_norm] at h
    simpa using h.trans hpd.le
  refine ⟨p, hpK, fun x hx => ?_⟩
  have i1 : Integrable (fun k => ψ k * F x 1) (muK ε) := hintC _ (ψ.continuous.mul continuous_const)
  have i2 : Integrable (fun k => ψ k * F x k) (muK ε) := hintC _ (ψ.continuous.mul (hFx x))
  have i3 : Integrable (fun k => p k * F x k) (muK ε) := hintC _ (p.continuous.mul (hFx x))
  have e1 : ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) = F x 1 - ∫ k, ψ k * F x k ∂(muK ε) := by
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hψint, one_mul]
  have e2 : ∫ k, (ψ k - p k) * F x k ∂(muK ε) =
      ∫ k, ψ k * F x k ∂(muK ε) - ∫ k, p k * F x k ∂(muK ε) := by
    simp_rw [sub_mul]
    exact integral_sub i2 i3
  have e3 : F x 1 - ∫ k, p k * F x k ∂(muK ε) =
      ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε) := by
    rw [e1, e2]; ring
  have b1 : ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε)‖ ≤ δ / 3 := by
    have hg : Integrable (fun k => f k / I * (δ / 3)) (muK ε) :=
      hintR _ ((f.continuous.div_const I).mul continuous_const)
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans_eq ?_
    · rw [norm_mul, hψnorm]
      by_cases hk : k ∈ U
      · have := hUP k hk x hx
        rw [norm_sub_rev] at this
        exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hfnn k) hIpos.le)
      · rw [hfU k hk]; simp
    · rw [integral_mul_const, integral_div, hIdef, div_self hIpos.ne', one_mul]
  have b2 : ‖∫ k, (ψ k - p k) * F x k ∂(muK ε)‖ ≤ δ / 3 := by
    refine (norm_integral_le_of_norm_le_const (C := δ / (3 * A) * M)
      (Filter.Eventually.of_forall fun k => ?_)).trans ?_
    · rw [norm_mul]
      exact mul_le_mul (hpk k) (hM (x, k) ⟨hx, Set.mem_univ _⟩) (norm_nonneg _) hη.le
    · calc δ / (3 * A) * M * (muK ε).real Set.univ
          = δ / (3 * A) * (M * (muK ε).real Set.univ) := by ring
        _ ≤ δ / (3 * A) * A := mul_le_mul_of_nonneg_left hMA hη.le
        _ = δ / 3 := by field_simp
  rw [e3]
  calc ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε)‖
      ≤ δ / 3 + δ / 3 := (norm_add_le _ _).trans (add_le_add b1 b2)
    _ < δ := by linarith

end GlobalTheory.KFinApprox
end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  first | exact @GlobalTheory.KSpan.finite_real_span | exact GlobalTheory.KSpan.finite_real_span | (intros; apply GlobalTheory.KSpan.finite_real_span <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.exists_spanning_lieAlgebra_coef_sq_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ C : ℝ, 0 ≤ C ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y := by
  first | exact @GlobalTheory.KGap.spanning_coef_bound | exact GlobalTheory.KGap.spanning_coef_bound | (intros; apply GlobalTheory.KGap.spanning_coef_bound <;> assumption)

end
end
