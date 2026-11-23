module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.Crv.Chain

open GlobalTheory.CompanionTheory.Ar.Crv

theorem abel_bound (ν v : ℕ → ℝ) (P : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hν : ∀ i, 1 ≤ i → i < n → ν (i + 1) ≤ ν i) (hv : ∀ i, i ≤ n → v i ≤ P) :
    ∑ i ∈ Finset.range n, ν (i + 1) * (v (i + 1) - v i) ≤
      ν n * v n - ν 1 * v 0 + P * (ν 1 - ν n) := by
  induction n, hn using Nat.le_induction with
  | base => simp; linarith
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun i h h' => hν i h (by omega)) (fun i h => hv i (by omega))
    have h2 := hν n hn (by omega)
    have h3 := hv n (by omega)
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]

theorem lmuNum_nonneg : ∀ (T : Type) [Fintype T] (p j q : ℕ) (μ w l : T → ℕ → ℝ) (P e : ℝ), 2 < p → 1 ≤ j → 1 ≤ q → GapCond p j q μ → (∀ τ, w τ 0 = 0) → (∀ τ, l τ 0 = 0) → (∀ τ i, i ≤ j → w τ i ≤ P) → (∀ τ i, i ≤ q → l τ i ≤ P) → (∀ τ, w τ j = l τ q) → e = -2 * ∑ τ, w τ j → ((p : ℝ) - 2) * P ≤ e → 0 ≤ e → 0 ≤ lmuNum j q μ w l := by
  intro T _ p j q μ w l P e hp hj hq hgap hw0 hl0 hw hl hwl he hPe he0
  obtain ⟨hdom, M, g, hM, hg, hpg⟩ := hgap
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ₀⟩⟩
  · simp [lmuNum]
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hP : 0 ≤ P := by have := hw τ₀ 0 (by omega); rwa [hw0] at this
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM τ₀ 1 le_rfl (by omega))
  have hf : (0 : ℝ) ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  have hfM : 0 ≤ (Fintype.card T : ℝ) * M := mul_nonneg hf hM0
  have hg0 : 0 ≤ g := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' (neg_pos.2 h)]
  have key : ∀ τ, (∑ i ∈ Finset.range j, μ τ (i + 1) * (w τ (i + 1) - w τ i)) +
      ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) ≤
      g * w τ j + 2 * M * P := by
    intro τ
    have hA := abel_bound (μ τ) (w τ) P j hj (fun i h h' => hdom τ i h (by omega)) (hw τ)
    have hB := abel_bound (fun i => μ τ (j + i)) (fun m => l τ (q - m)) P q hq
      (fun i h h' => hdom τ (j + i) (by omega) (by omega)) (fun i _ => hl τ _ (by omega))
    simp only [Nat.sub_self, Nat.sub_zero, hl0, ← hwl τ] at hB
    rw [hw0] at hA
    have e1 : ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) =
        ∑ m ∈ Finset.range q, μ τ (j + (m + 1)) * (l τ (q - (m + 1)) - l τ (q - m)) := rfl
    rw [e1]
    have h1 := abs_le.1 (hM τ 1 le_rfl (by omega))
    have h2 := abs_le.1 (hM τ (j + q) (by omega) le_rfl)
    have h3 := mul_nonneg (sub_nonneg.2 (hg τ)) (sub_nonneg.2 (hw τ j le_rfl))
    have h4 : 0 ≤ P * (2 * M - (μ τ 1 - μ τ (j + q))) := mul_nonneg hP (by linarith [h1.2, h2.1])
    have h5 := mul_nonneg hg0 hP
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun τ _ => key τ)
  rw [Finset.sum_add_distrib (f := fun τ => g * w τ j), ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hS : ∑ τ, w τ j = -e / 2 := by linarith
  rw [hS] at hsum
  have hfin : g * (-e / 2) + (Fintype.card T : ℝ) * (2 * M * P) ≤ 0 := by
    have a1 := mul_le_mul_of_nonneg_left hPe hfM
    have a2 := mul_le_mul_of_nonneg_right hpg he0
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' h]
  unfold lmuNum
  linarith

end GlobalTheory.CompanionTheory.Ar.Crv.Chain
end

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem xiPot_logSin_change_of_frame : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  intro G g hG hg
  have herm2_conj_lemma : ∀ (u w : Fin 2 → ℂ), herm2 (gᴴ * G * g) u w = herm2 G (g *ᵥ u) (g *ᵥ w) := by
    intro u w
    unfold herm2
    rw [← Matrix.mulVec_mulVec w (gᴴ * G) g, ← Matrix.mulVec_mulVec (g *ᵥ w) gᴴ G,
      Matrix.dotProduct_mulVec (star u) gᴴ, Matrix.star_mulVec g u]
  have herm2_smul_lemma_2 : ∀ (s t : ℂ) (u w : Fin 2 → ℂ),
      herm2 G (s • u) (t • w) = star s * t * herm2 G u w := by
    intro s t u w
    have hsu : star (s • u) = star s • star u := by
      ext i
      simp [star_mul']
    unfold herm2
    rw [Matrix.mulVec_smul, hsu, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have ratio_lemma_3 : ∀ (x y p q r : ℝ), x ≠ 0 → y ≠ 0 →
      (x * y * r) ^ 2 / (x ^ 2 * p * (y ^ 2 * q)) = r ^ 2 / (p * q) := by
    intro x y p q r hx hy
    rw [show (x * y * r) ^ 2 = r ^ 2 * (x ^ 2 * y ^ 2) by ring,
      show x ^ 2 * p * (y ^ 2 * q) = (p * q) * (x ^ 2 * y ^ 2) by ring]
    exact mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hy))
  have hdet : g.det ≠ 0 := hg.ne_zero
  have hv : ∀ b : ℂ, (![1, b] : Fin 2 → ℂ) ≠ 0 := by
    intro b h
    have h0 := congrFun h 0
    simp at h0
  have hre : ∀ b : ℂ, 0 < (herm2 G ![1, b] ![1, b]).re := fun b =>
    (Complex.pos_iff.1 (hG.dotProduct_mulVec_pos (hv b))).1
  have hdG : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hcc : ∀ c : ℂ, star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    intro c
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hre_mul : ∀ c z : ℂ, (star c * c * z).re = ‖c‖ ^ 2 * z.re := by
    intro c z
    rw [hcc, Complex.re_ofReal_mul]
  have hc : ∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → g *ᵥ ![1, a] =
      (g 0 0 + g 0 1 * a) • ![1, (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)] := by
    intro a ha
    have ha' : g 0 0 + a * g 0 1 ≠ 0 := by rwa [mul_comm a]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  refine ⟨hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg)), ?_, ?_⟩
  · intro a ha
    unfold xiPot
    rw [herm2_conj_lemma, hc a ha, herm2_smul_lemma_2, hre_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_conjTranspose,
      show star g.det * G.det * g.det = star g.det * g.det * G.det by ring, hre_mul,
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)) (hre _).ne',
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hdet)) hdG.ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  · intro a₀ a₁ h₀ h₁
    unfold logSin
    rw [herm2_conj_lemma, herm2_conj_lemma, herm2_conj_lemma, hc a₀ h₀, hc a₁ h₁, herm2_smul_lemma_2,
      herm2_smul_lemma_2, herm2_smul_lemma_2, hre_mul, hre_mul, norm_mul, norm_mul, norm_star,
      ratio_lemma_3 _ _ _ _ _ (norm_ne_zero_iff.mpr h₀) (norm_ne_zero_iff.mpr h₁)]

end GlobalTheory.CompanionTheory.Ar.PB
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

private theorem sum_eq_sum_comp_of_eq_zero_of_forall_ne {ι κ M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [AddCommMonoid M] (v : κ → ι) (hv : Function.Injective v) (f : ι → M)
    (hf : ∀ i, (∀ a, i ≠ v a) → f i = 0) :
    ∑ i, f i = ∑ a, f (v a) := by
  rw [← Finset.sum_image (f := f) (s := Finset.univ) (g := v) (fun a _ b _ h => hv h)]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hf i (fun a hia =>
    hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hia.symm⟩)))).symm

theorem gramOf_mul {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ) :
    gramOf hd (u * g) = gᴴ * gramOf hd u * g := by
  simp only [GlobalTheory.CompanionTheory.Ar.PB.gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem head_conj_mul {N : ℕ} {P : Type*} [Fintype P] (v : P → Fin N)
    (hv : Function.Injective v) (hdown : ∀ (i : Fin N) (c : P), (∀ a, i ≠ v a) → v c < i)
    (G b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) :
    (bᴴ * G * b).submatrix v v = (b.submatrix v v)ᴴ * G.submatrix v v * b.submatrix v v := by
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
    intro i hi
    rw [hb (hdown i p hi), star_zero, zero_mul]
  · intro j hj
    rw [hb (hdown j q hj), mul_zero]

theorem gramLog_inv (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧
    (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 →
      gramLog hd k (g * b) = gramLog hd k g +
        ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  constructor
  · intro h
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog, GlobalTheory.CompanionTheory.Ar.PB.gramHead]
    rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul, h, GlobalTheory.CompanionTheory.Ar.PB.gramOf]
  · intro hb hdet hM
    have hdown : ∀ (i : Fin N) (c : {a : Fin N // (a : ℕ) < k}),
        (∀ a : {a : Fin N // (a : ℕ) < k}, i ≠ a.val) → c.val < i := by
      intro i c hi
      have hik : ¬ (i : ℕ) < k := fun h => hi ⟨i, h⟩ rfl
      rw [Fin.lt_def]
      exact lt_of_lt_of_le c.2 (not_lt.mp hik)
    have hbk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).IsUpperTriangular :=
      fun i j hij => hb (Subtype.coe_lt_coe.mpr hij)
    have hdiag : ∀ i, b i i ≠ 0 := by
      intro i hi
      have h0 : b.det = 0 := by
        rw [Matrix.det_of_upperTriangular hb]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [h0] at hdet
      exact not_isUnit_zero hdet
    have hdetk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).det = ∏ a : {a : Fin N // (a : ℕ) < k}, b a a :=
      Matrix.det_of_upperTriangular hbk
    have hminor : GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b) =
        (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val)ᴴ *
          GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g *
            b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val := by
      simp only [GlobalTheory.CompanionTheory.Ar.PB.gramHead]
      rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul]
      exact GlobalTheory.CompanionTheory.Ar.PB.head_conj_mul Subtype.val
        Subtype.val_injective hdown _ b hb
    have hB0 : ∏ a : {a : Fin N // (a : ℕ) < k}, b a a ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun a _ => hdiag a)
    have hnorm : ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b)).det‖ =
        ‖∏ a : {a : Fin N // (a : ℕ) < k}, b a a‖ ^ 2 *
          ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g).det‖ := by
      rw [hminor, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetk, norm_mul,
        norm_mul, norm_star]
      ring
    have hsum : (∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) =
        ∑ a : {a : Fin N // (a : ℕ) < k}, Real.log ‖b a a‖ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun a => by simp) _
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog]
    rw [hnorm, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hB0)) (norm_ne_zero_iff.mpr hM),
      Real.log_pow, norm_prod, Real.log_prod (s := Finset.univ)
        (f := fun a : {a : Fin N // (a : ℕ) < k} => ‖b a a‖) (fun a _ => norm_ne_zero_iff.mpr (hdiag a)),
      hsum]
    push_cast
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial

theorem killNone_formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) :
    aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) (formPoly n a)
      = formPoly n fun w => a fun j => some (w j) := by
  classical
  unfold formPoly

  rw [map_sum]
  symm
  refine Finset.sum_of_injOn (fun (w : Fin n → σ) j => some (w j)) ?_ ?_ ?_ ?_
  · intro w _ w' _ h
    funext j
    exact Option.some_injective _ (congrFun h j)
  · intro w _
    exact Finset.mem_univ _
  · intro w _ hw
    have : ∃ j, w j = none := by
      by_contra hc
      apply hw
      have hc' : ∀ j, (w j).isSome := fun j => by
        cases h : w j with
        | none => exact absurd ⟨j, h⟩ hc
        | some _ => rfl
      exact ⟨fun j => (w j).get (hc' j), Finset.mem_coe.2 (Finset.mem_univ _), by funext j; simp⟩
    obtain ⟨j, hj⟩ := this
    rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro w _
    simp [map_prod]

theorem killNone_toWtS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) :
    aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) (toWtS Q)
      = toWt (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) Q) := by
  have h : (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)).comp toWtS
      = toWt.comp (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)) := by
    apply MvPolynomial.algHom_ext
    intro o
    cases o with
    | none => simp [toWtS, toWt]
    | some p =>
      simp only [toWtS, toWt, AlgHom.comp_apply, aeval_X, Option.elim_some, aeval_rename]
      have : ((fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) ∘ some) = X := rfl
      rw [this, aeval_X_left_apply]
  exact DFunLike.congr_fun h Q

theorem eval_toWt_gap {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ) :
    eval lam (toWt Q) = eval (gap lam) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWt]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [toWt, gap]

theorem eval_toWtS_gapS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ)
    (s : ℝ) : eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWtS]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    cases i with
    | none => simp [toWtS, gapS]
    | some q =>
      simp only [toWtS, gapS, gap, aeval_X, eval_X, Option.elim_some, eval_rename]
      rfl

theorem poly_s_zero : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ),
    (∀ (a : (Fin n → Option (Ψ × Fin N)) → ℝ),
      aeval (fun o : Option (Ψ × Fin N) => o.elim 0 X) (toWtS (formPoly n a))
        = toWt (formPoly n fun w => a fun j => some (w j))) ∧
    (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ), eval lam (toWt Q) = eval (gap lam) Q) ∧
    ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ) (s : ℝ),
      eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  intro Ψ _ N n
  refine ⟨fun a => ?_, eval_toWt_gap, eval_toWtS_gapS⟩
  rw [killNone_toWtS, killNone_formPoly]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem abs_coeff_prod_X_le_one {σ : Type} {n : ℕ} (w : Fin n → σ) (m : σ →₀ ℕ) :
    |(∏ j, X (w j) : MvPolynomial σ ℝ).coeff m| ≤ 1 := by
  classical
  have h : (∏ j, X (w j) : MvPolynomial σ ℝ) = monomial (∑ j, Finsupp.single (w j) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [h, coeff_monomial]
  split_ifs <;> simp

theorem formPoly_sub_bound : ∀ (σ : Type) [Fintype σ] (n : ℕ) (a b : (Fin n → σ) → ℝ) (M : ℝ),
    (∀ w, |a w - b w| ≤ M) →
    (∀ m, |(formPoly n a).coeff m - (formPoly n b).coeff m| ≤ (Fintype.card σ : ℝ) ^ n * M) ∧
    ∀ c : σ → ℝ, |eval c (formPoly n a) - eval c (formPoly n b)| ≤ (∑ x, |c x|) ^ n * M := by
  intro σ _ n a b M h
  constructor
  · intro m
    simp only [formPoly, coeff_sum, coeff_C_mul]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * (∏ j, X (w j) : MvPolynomial σ ℝ).coeff m
            - b w * (∏ j, X (w j) : MvPolynomial σ ℝ).coeff m|
        ≤ ∑ _w : Fin n → σ, M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul]
          calc _ ≤ |a w - b w| * 1 :=
                mul_le_mul_of_nonneg_left (abs_coeff_prod_X_le_one w m) (abs_nonneg _)
            _ ≤ M := by rw [mul_one]; exact h w
      _ = (Fintype.card σ : ℝ) ^ n * M := by
          simp
  · intro c

    simp only [formPoly, map_sum, map_mul, eval_C, map_prod, eval_X]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * ∏ j, c (w j) - b w * ∏ j, c (w j)|
        ≤ ∑ w : Fin n → σ, (∏ j, |c (w j)|) * M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul, Finset.abs_prod, mul_comm]
          exact mul_le_mul_of_nonneg_left (h w) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = (∑ x, |c x|) ^ n * M := by
          rw [← Finset.sum_mul, Fintype.sum_pow]

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gap_eq_weight_sub_next {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap lam p = lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0 := by
  unfold gap gapX
  split_ifs <;> simp

theorem gap_comp_swap {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (hb : (b : ℕ) = a + 1)
    (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = gap lam p + gap lam (τ, a) * (xiCoef τ a p : ℝ) := by
  have hab : (a : ℕ) + 1 < N := hb ▸ b.2
  have hbe : (⟨(a : ℕ) + 1, hab⟩ : Fin N) = b := Fin.ext hb.symm
  have hu : gap lam (τ, a) = lam (τ, a) - lam (τ, b) := by
    rw [gap_eq_weight_sub_next]; simp only [hab, dif_pos, hbe]
  have hsw : ∀ q : Ψ × Fin N, (lam ∘ Equiv.swap (τ, a) (τ, b)) q =
      lam q + (if q.1 = τ then (if (q.2 : ℕ) = a + 1 then 1 else 0) - (if (q.2 : ℕ) = a then 1 else 0) else 0)
        * (lam (τ, a) - lam (τ, b)) := by
    rintro ⟨σ, i⟩
    by_cases h1 : (σ, i) = (τ, a)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      simp
    by_cases h2 : (σ, i) = (τ, b)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      simp [hb]
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
    by_cases hσ : σ = τ
    · subst hσ
      have e1 : (i : ℕ) ≠ a := fun h => h1 (by rw [Fin.ext h])
      have e2 : (i : ℕ) ≠ a + 1 := fun h => h2 (by rw [Fin.ext (h.trans hb.symm)])
      simp [e1, e2]
    · simp [hσ]
  obtain ⟨σ, i⟩ := p
  rw [hu, gap_eq_weight_sub_next, gap_eq_weight_sub_next]
  simp only [hsw, xiCoef, Fin.ext_iff]
  have hi := i.2
  split_ifs <;> first | omega | (push_cast; ring)

theorem gap_swap_decomp : ∀ (Ψ : Type) [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ∀ lam : Ψ × Fin N → ℝ, let u := gap lam (τ, a); let c := fun p => gap lam p + u / 2 * (xiCoef τ a p : ℝ); c (τ, a) = 0 ∧ (∀ p, gap lam p = c p - u / 2 * (xiCoef τ a p : ℝ)) ∧ ∀ p, gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = c p + u / 2 * (xiCoef τ a p : ℝ) := by
  intro Ψ _ N τ a b hb lam u c
  refine ⟨?_, fun p => ?_, fun p => ?_⟩
  · simp only [c, u, xiCoef]
    simp
  · simp only [c]; ring
  · rw [gap_comp_swap τ a b hb]
    simp only [c, u]; ring

end GlobalTheory.CompanionTheory.Ar.PB
end
