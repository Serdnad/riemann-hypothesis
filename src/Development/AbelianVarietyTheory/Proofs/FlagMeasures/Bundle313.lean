module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

noncomputable section

open MeasureTheory Metric
open scoped Matrix

namespace GlobalTheory.UJGrowth

variable {n : ℕ} {ε : Fin n → Bool}

def ent (g : Formalism.REAL.UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (Formalism.MainNotions.S.uMat g)

theorem ent_closedEmb : Topology.IsClosedEmbedding (ent (ε := ε)) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1

theorem mem_closedBall_iff_entries {x y : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall y R ↔ ∀ i j, ‖x i j - y i j‖ ≤ R := by
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR]
  exact forall_congr' fun i => pi_norm_le_iff_of_nonneg hR

theorem mem_closedBall_zero_iff_entries {x : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall 0 R ↔ ∀ i j, ‖x i j‖ ≤ R := by
  rw [mem_closedBall_iff_entries hR]
  simp

theorem uMat_inv_mul' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g⁻¹ * g) = Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g from rfl, inv_mul_cancel]
  rfl

theorem uMat_mul_inv' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g * g⁻¹) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

theorem uMat_inv_eq (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ = Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.MainNotions.S.uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc Formalism.MainNotions.S.uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g) * Formalism.MainNotions.S.uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv', Matrix.mul_one]

theorem norm_inv_entry (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖Formalism.MainNotions.S.uMat g⁻¹ i j‖ = ‖Formalism.MainNotions.S.uMat g j i‖ := by
  rw [uMat_inv_eq]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem small_ball {S : Subgroup (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (h : (n : ℝ) * (R * (2 * δ)) ≤ 1) (x : Fin n → Fin n → ℂ) :
    μ (ent ⁻¹' (closedBall 0 R ∩ closedBall x δ)) ≤
      μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) := by
  by_cases hex : ∃ s ∈ ent ⁻¹' (closedBall 0 R ∩ closedBall x δ), s ∈ S
  · obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := hex
    have hme : MeasurableEmbedding (fun t : Formalism.REAL.UJ ε => s * t) :=
      (Homeomorph.mulLeft s).isClosedEmbedding.measurableEmbedding
    conv_lhs => rw [← hμ.2.2.2 s hs]
    rw [hme.map_apply]
    refine measure_mono fun t ht => ?_
    have ht2 : ent (s * t) ∈ closedBall x δ := ht.2
    have h1 : ent (s * t) ∈ closedBall (ent s) (2 * δ) := by
      have := dist_triangle_right (ent (s * t)) (ent s) x
      rw [mem_closedBall]
      linarith [mem_closedBall.1 ht2, mem_closedBall.1 hs2]
    rw [Set.mem_preimage, mem_closedBall_iff_entries zero_le_one]
    intro i j
    have e : Formalism.MainNotions.S.uMat t = Formalism.MainNotions.S.uMat s⁻¹ * Formalism.MainNotions.S.uMat (s * t) := by
      rw [show Formalism.MainNotions.S.uMat (s * t) = Formalism.MainNotions.S.uMat s * Formalism.MainNotions.S.uMat t from rfl, ← Matrix.mul_assoc,
        uMat_inv_mul', Matrix.one_mul]
    have e2 : Formalism.MainNotions.S.uMat t - 1 =
        Formalism.MainNotions.S.uMat s⁻¹ * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) := by
      rw [Matrix.mul_sub, ← e, uMat_inv_mul']
    have e3 : ent t i j - ent (1 : Formalism.REAL.UJ ε) i j = (Formalism.MainNotions.S.uMat t - 1) i j := rfl
    rw [e3, e2, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ l ∈ (Finset.univ : Finset (Fin n)),
        ‖Formalism.MainNotions.S.uMat s⁻¹ i l * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) l j‖ ≤ R * (2 * δ) :=
      fun l _ => by
        rw [norm_mul]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) hR
        · rw [norm_inv_entry]
          exact (mem_closedBall_zero_iff_entries hR).1 hs1 l i
        · exact (mem_closedBall_iff_entries (by linarith)).1 h1 l j
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    simpa using h
  · rw [measure_mono_null (t := (S : Set (Formalism.REAL.UJ ε))ᶜ) (fun s hs hS => hex ⟨s, hs, hS⟩) hμ.2.2.1]
    exact zero_le

end GlobalTheory.UJGrowth

namespace GlobalTheory.UJGrowth

theorem growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε),
    Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ →
    ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R →
      μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  intro n ε S _ μ hμ hfin
  haveI := hμ.1
  have hemb : Topology.IsClosedEmbedding (ent (ε := ε)) := ent_closedEmb
  let ν : Measure (Fin n → Fin n → ℂ) := μ.map ent
  have hνA : ∀ A, MeasurableSet A → ν A = μ (ent ⁻¹' A) := fun A hA =>
    Measure.map_apply hemb.continuous.measurable hA
  have hcpt : ∀ y r, μ (ent ⁻¹' closedBall y r) < ⊤ := fun y r =>
    (hemb.isCompact_preimage (isCompact_closedBall y r)).measure_lt_top
  haveI : SigmaFinite ν := hemb.measurableEmbedding.sigmaFinite_map
  set M := μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) with hM
  have hMf : M ≠ ⊤ := (hcpt _ _).ne
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set d := Module.finrank ℝ (Fin n → Fin n → ℂ)
  let lam : Measure (Fin n → Fin n → ℂ) := Measure.addHaar
  refine ⟨M.toReal * (4 * N) ^ d, 2 * d, fun R hR => ?_⟩
  set δ := (2 * N * R)⁻¹ with hδ
  have hp : 1 ≤ 2 * N * R := by nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hcond : (n : ℝ) * (R * (2 * δ)) ≤ 1 := by
    have e : (n : ℝ) * (R * (2 * δ)) = n / N := by
      rw [hδ]; field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hsb : ∀ x, ν (closedBall 0 R ∩ closedBall x δ) ≤ M := fun x => by
    rw [hνA _ (measurableSet_closedBall.inter measurableSet_closedBall)]
    exact small_ball hμ (by linarith) hδ0.le hcond x
  have hset : {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} = ent ⁻¹' closedBall 0 R := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff_entries (by linarith)]
    rfl
  rw [hset, ← hνA _ measurableSet_closedBall]
  let W : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) := {p | p.1 ∈ closedBall 0 R ∧ dist p.1 p.2 ≤ δ}
  have hW : MeasurableSet W :=
    ((isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le continuous_dist continuous_const)).measurableSet
  have e1 : (ν.prod lam) W = lam (closedBall 0 δ) * ν (closedBall 0 R) := by
    rw [Measure.prod_apply hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ closedBall (0 : Fin n → Fin n → ℂ) R
    · rw [Set.indicator_of_mem hs, ← Measure.addHaar_closedBall_center lam s]
      congr 1
      ext x
      exact ⟨fun h => mem_closedBall'.2 h.2, fun h => ⟨hs, mem_closedBall'.1 h⟩⟩
    · rw [Set.indicator_of_notMem hs]
      have : Prod.mk s ⁻¹' W = ∅ := by
        ext x
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, hs, false_and, Set.mem_empty_iff_false]
      rw [this, measure_empty]
  have e2 : (ν.prod lam) W ≤ M * lam (closedBall 0 (2 * R)) := by
    rw [Measure.prod_apply_symm hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Fin n → Fin n → ℂ) (2 * R)
    · rw [Set.indicator_of_mem hx]
      exact hsb x
    · have : (fun s => (s, x)) ⁻¹' W = ∅ := by
        ext s
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, mem_closedBall]
        rintro ⟨h1, h2⟩
        apply hx
        have := dist_triangle_left x 0 s
        rw [mem_closedBall]; linarith
      simp [this]
  rw [e1, Measure.addHaar_closedBall lam _ hδ0.le, Measure.addHaar_closedBall lam _ (by linarith)] at e2
  have hb0 : 0 < (lam (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos lam _ one_pos).ne' measure_ball_lt_top.ne
  have e3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hMf
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)) e2
  simp only [ENNReal.toReal_mul] at e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at e3
  have e4 : δ ^ d * (ν (closedBall 0 R)).toReal ≤ M.toReal * (2 * R) ^ d := by
    refine le_of_mul_le_mul_right ?_ hb0
    calc _ = δ ^ d * (lam (ball 0 1)).toReal * (ν (closedBall 0 R)).toReal := by ring
      _ ≤ _ := e3
      _ = _ := by ring
  have e5 : M.toReal * (2 * R) ^ d = δ ^ d * (M.toReal * (4 * N) ^ d * R ^ (2 * d)) := by
    have : 2 * R = δ * (4 * N) * R ^ 2 := by rw [hδ]; field_simp; ring
    rw [this, mul_pow, mul_pow, pow_mul]; ring
  rw [e5] at e4
  have e6 := le_of_mul_le_mul_left e4 (by positivity)
  have hνf : ν (closedBall 0 R) ≠ ⊤ := by
    rw [hνA _ measurableSet_closedBall]; exact (hcpt _ _).ne
  rw [← ENNReal.ofReal_toReal hνf]
  exact ENNReal.ofReal_le_ofReal e6

end GlobalTheory.UJGrowth
end
end

section

noncomputable section

namespace GlobalTheory.PointStab

open Formalism.MainNotions.S

theorem ptEntry_monomial {K : Type} [Field K] (bs : List (K × ℕ)) (hbs : ∀ b ∈ bs, b.1 ≠ 0) :
    ∃ (σ : ℕ → ℕ) (t : ℕ → K), ∀ a, a < (bs.map Prod.snd).sum →
      σ a < (bs.map Prod.snd).sum ∧ σ (σ a) = a ∧
      Formalism.L2.SG.RealObj.blkOf bs (σ a) = Formalism.L2.SG.RealObj.blkOf bs a ∧ t a ≠ 0 ∧
      ∀ b, b < (bs.map Prod.snd).sum →
        (a ≤ b → Formalism.L2.SG.RealObj.blkOf bs a ≤ Formalism.L2.SG.RealObj.blkOf bs b) ∧
        (Formalism.L2.SG.RealObj.blkOf bs a = Formalism.L2.SG.RealObj.blkOf bs b → a + σ a = b + σ b) ∧
        ptEntry bs a b = if b = σ a then t a else 0 := by
  induction bs with
  | nil => exact ⟨id, fun _ => 1, fun a ha => by simp at ha⟩
  | cons x bs ih =>
    obtain ⟨t0, m⟩ := x
    have ht0 : t0 ≠ 0 := hbs _ (List.mem_cons_self ..)
    obtain ⟨σ, t, h⟩ := ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map Prod.snd).sum = N at h ⊢
    refine ⟨fun a => if a < m then m - 1 - a else σ (a - m) + m,
      fun a => if a < m then t0 else t (a - m), fun a ha => ?_⟩
    simp only [Formalism.L2.SG.RealObj.blkOf, ptEntry]
    by_cases h1 : a < m
    · have h2 : m - 1 - a < m := by omega
      simp only [h1, h2, if_true]
      refine ⟨by omega, by omega, trivial, ht0, fun b hb => ?_⟩
      by_cases h3 : b < m
      · simp only [h3, if_true, and_self]
        refine ⟨fun _ => le_refl _, fun _ => by omega, ?_⟩
        have : a + b + 1 = m ↔ b = m - 1 - a := by omega
        simp [this]
      · have h4 : ¬ m ≤ a := by omega
        have h5 : ¬ b = m - 1 - a := by omega
        simp [h3, h4, h5]
    · obtain ⟨e1, e2, e3, e0, e4⟩ := h (a - m) (by omega)
      have h2 : ¬ σ (a - m) + m < m := by omega
      have h4 : m ≤ a := by omega
      simp only [h1, h2, if_false, Nat.add_sub_cancel, e2, e3]
      refine ⟨by omega, by omega, trivial, e0, fun b hb => ?_⟩
      by_cases h3 : b < m
      · have h5 : ¬ m ≤ b := by omega
        have h6 : ¬ b = σ (a - m) + m := by omega
        have h7 : ¬ a ≤ b := by omega
        simp [h3, h5, h6, h7]
      · obtain ⟨f1, f2, f3⟩ := e4 (b - m) (by omega)
        have h5 : m ≤ b := by omega
        have h6 : b = σ (a - m) + m ↔ b - m = σ (a - m) := by omega
        simp only [h3, h5, h4, if_false, h6, f3, and_self, and_false, and_true]
        refine ⟨fun hab => ?_, fun hab => ?_, by simp⟩
        · have := f1 (by omega); omega
        · have := f2 (by omega); omega

theorem mul_mono {E : Type} [CommRing E] {n : ℕ} (σ : Fin n → Fin n) (hσ : ∀ a, σ (σ a) = a) (c : Fin n → E)
    (Z : Matrix (Fin n) (Fin n) E) (hZ : ∀ a b, Z a b = if b = σ a then c a else 0)
    (X Y : Matrix (Fin n) (Fin n) E) :
    X * Z = Z * Y ↔ ∀ i a, X i a * c a = c i * Y (σ i) (σ a) := by
  have h1 : ∀ i a, (X * Z) i (σ a) = X i a * c a := by
    intro i a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp [hZ]
    · intro k _ hk
      have : ¬ σ a = σ k := fun h => hk (by rw [← hσ k, ← h, hσ])
      simp [hZ, this]
    · simp
  have h2 : ∀ i j, (Z * Y) i j = c i * Y (σ i) j := by
    intro i j
    simp [Matrix.mul_apply, hZ]
  constructor
  · intro h i a; rw [← h1, h, h2]
  · intro h; ext i j; rw [← hσ j, h1, h2, h]

end GlobalTheory.PointStab

namespace GlobalTheory.PointStab

open Formalism.MainNotions.S

theorem stab_blockDiag : ∀ {K : Type} [Field K] (sig : K →+* K), (∀ x, sig (sig x) = x) → ∀ (r : ℕ) (w : Formalism.MainNotions.S.Point K (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K), Formalism.MainNotions.S.ZhatOM Z = Formalism.MainNotions.S.ptMat w → (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s → Formalism.MainNotions.S.IsUpUni s' → (s.map sig).transpose * Z * s' = Z → ∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) ∧ ∀ s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s' → (∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s ∧ (s.map sig).transpose * Z * s' = Z := by
  intro K _ sig hsig r w Z hZ
  obtain ⟨σ, t, h⟩ := ptEntry_monomial w.1 (fun b hb => (w.2.1 b hb).1)
  rw [w.2.2] at h
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ a, (h a a.2).1⟩
  let β : Fin (r + 1) → ℕ := fun a => Formalism.L2.SG.RealObj.blkOf w.1 a.1
  let c : Fin (r + 1) → K := fun a => (-1) ^ (r - σ a) * t a
  have hc : ∀ a, c a ≠ 0 := fun a => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h a a.2).2.2.2.1
  have hσ : ∀ a, σ' (σ' a) = a := fun a => Fin.ext (h a a.2).2.1
  have hβσ : ∀ a, β (σ' a) = β a := fun a => (h a a.2).2.2.1
  have hlt : ∀ a b, β a < β b → a < b := fun a b hab => by
    by_contra h'
    exact absurd (((h b b.2).2.2.2.2 a a.2).1 (not_lt.1 h')) (not_le.2 hab)
  have hrev : ∀ a b, β a = β b → a < b → σ' b < σ' a := fun a b hab hl => by
    have h1 := ((h a a.2).2.2.2.2 b b.2).2.1 hab
    have h2 : (a : ℕ) < b := hl
    show σ b < σ a
    omega
  have hZ' : ∀ a b, Z a b = if b = σ' a then c a else 0 := by
    intro a b
    have e0 := congrFun (congrFun hZ a) b
    simp only [ZhatOM, ptMat] at e0
    have e : Z a b = (-1) ^ (r - b.val) * ptEntry w.1 a b := by
      rw [← e0, ← mul_assoc, ← mul_pow]; simp
    rw [e, ((h a a.2).2.2.2.2 b b.2).2.2]
    by_cases hb : b = σ' a
    · subst hb; simp [σ', c]
    · have h3 : ¬ (b : ℕ) = σ a := fun h' => hb (Fin.ext h')
      simp [hb, h3]
  have hmm := mul_mono σ' hσ c Z hZ'
  have hLapp : ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ∀ i a, (s.map sig).transpose i a = sig (s a i) :=
    fun s i a => rfl
  refine ⟨fun s s' hs hs' hE a b hab => ?_, fun s' hs' hbd => ?_⟩
  · generalize hLdef : (s.map sig).transpose = L at hE
    have hLapp' : ∀ i a, L i a = sig (s a i) := fun i a => by rw [← hLdef]; rfl
    have hLT : L.BlockTriangular OrderDual.toDual := fun i j hij => by
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      rw [hLapp', (hs j i).1 hij', map_zero]
    have hdet : L.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L hLT]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hLapp', (hs i i).2 rfl, map_one]
    have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
    letI : Invertible L := Matrix.invertibleOfIsUnitDet L hu
    have hBT := Matrix.blockTriangular_inv_of_blockTriangular hLT
    have e : L⁻¹ * Z = Z * s' := by
      calc L⁻¹ * Z = L⁻¹ * (L * Z * s') := by rw [hE]
        _ = Z * s' := by
          rw [Matrix.mul_assoc L, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [hmm] at e
    rcases lt_or_gt_of_ne hab with h1 | h1
    · have h2 : σ' a < σ' b := hlt _ _ (by rw [hβσ, hβσ]; exact h1)
      have h3 := e (σ' a) (σ' b)
      rw [hσ, hσ, hBT (OrderDual.toDual_lt_toDual.2 h2), zero_mul, eq_comm] at h3
      exact (mul_eq_zero.1 h3).resolve_left (hc _)
    · exact (hs' a b).1 (hlt _ _ h1)
  · have hs'T : s'.BlockTriangular id := fun i j hij => (hs' i j).1 hij
    have hdet : s'.det = 1 := by
      rw [Matrix.det_of_upperTriangular hs'T]
      exact Finset.prod_eq_one fun i _ => (hs' i i).2 rfl
    have hu : IsUnit s'.det := by rw [hdet]; exact isUnit_one
    letI : Invertible s' := Matrix.invertibleOfIsUnitDet s' hu
    have hUup := Matrix.blockTriangular_inv_of_blockTriangular hs'T
    have hs'β : s'.BlockTriangular (OrderDual.toDual ∘ β) := fun i j hij =>
      hbd i j (ne_of_lt (OrderDual.toDual_lt_toDual.1 hij))
    have hUβ := Matrix.blockTriangular_inv_of_blockTriangular hs'β
    have hsU : s' * s'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have hUs : s'⁻¹ * s' = 1 := Matrix.nonsing_inv_mul _ hu
    generalize s'⁻¹ = U at hUup hUβ hsU hUs
    have hUdiag : ∀ i, U i i = 1 := by
      intro i
      have h1 : (s' * U) i i = 1 := by rw [hsU]; simp
      rw [Matrix.mul_apply, Finset.sum_eq_single i, (hs' i i).2 rfl, one_mul] at h1
      · exact h1
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [(hs' i k).1 h, zero_mul]
        · rw [hUup (show id i < id k from h), mul_zero]
      · simp
    let s : Matrix (Fin (r + 1)) (Fin (r + 1)) K := fun a i => sig (c i * U (σ' i) (σ' a) / c a)
    have hs : IsUpUni s := by
      intro a i
      refine ⟨fun hia => ?_, fun hai => ?_⟩
      · have h0 : U (σ' i) (σ' a) = 0 := by
          rcases lt_trichotomy (β i) (β a) with h1 | h1 | h1
          · exact hUβ (OrderDual.toDual_lt_toDual.2 (by rw [hβσ, hβσ]; exact h1))
          · exact hUup (show id (σ' a) < id (σ' i) from hrev _ _ h1 hia)
          · exact absurd (hlt _ _ h1) (not_lt.2 hia.le)
        simp [s, h0]
      · subst hai
        simp [s, hUdiag, hc a]
    refine ⟨s, hs, ?_⟩
    have e : (s.map sig).transpose * Z = Z * U := by
      rw [hmm]
      intro i a
      rw [hLapp]
      simp only [s, hsig]
      exact div_mul_cancel₀ _ (hc a)
    rw [e, Matrix.mul_assoc, hUs, Matrix.mul_one]

end GlobalTheory.PointStab
end
end
