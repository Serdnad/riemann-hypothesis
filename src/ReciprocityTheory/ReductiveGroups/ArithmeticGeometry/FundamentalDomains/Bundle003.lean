module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Lemmata.GeneralBFactAltForm.Imports
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.SemistableReduction.Bundle002
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := NumberField.IsCMField.complexEmbedding_complexConj E τ x

section herm

variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

lemma hermC_emb (x y : Fin r → E) :
    hermC τ G (fun a => τ (x a)) (fun a => τ (y a)) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, map_sum, map_mul, emb_cc']

end herm

section flowAlg

variable (X : Data E r)

def wv (ξ : Fin r → E) (τ : X.Ψ) : Fin r → ℂ := fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))

lemma wv_dot (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) :
    wv X ξ τ ⬝ᵥ v = hermC τ.1 X.Gm v (Data.emb τ.1 ξ) := by
  simp only [dotProduct, wv, hermC, Data.emb, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma wv_dot_self {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    wv X ξ τ ⬝ᵥ Data.emb τ.1 ξ = 0 := by
  rw [wv_dot]
  exact (hermC_emb τ.1 X.Gm ξ ξ).trans (by rw [hξ, map_zero])

lemma flowMat_eq (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) :
    X.flowMat ξ τ s = 1 + (-(I * X.c τ * s)) • vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    vecMulVec_apply, wv, Data.emb, smul_eq_mul]
  ring

lemma nil_sq {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) * vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) = 0 := by
  ext a b
  have h0 := wv_dot_self X hξ τ
  simp only [dotProduct] at h0
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
  calc ∑ k, Data.emb τ.1 ξ a * wv X ξ τ k * (Data.emb τ.1 ξ k * wv X ξ τ b)
      = Data.emb τ.1 ξ a * wv X ξ τ b * ∑ k, wv X ξ τ k * Data.emb τ.1 ξ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = 0 := by rw [h0, mul_zero]

lemma flowMat_mul {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s s' : ℂ) :
    X.flowMat ξ τ s * X.flowMat ξ τ s' = X.flowMat ξ τ (s + s') := by
  rw [flowMat_eq, flowMat_eq, flowMat_eq]
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, nil_sq X hξ,
    smul_zero, smul_zero, add_zero, add_assoc, ← add_smul]
  congr 2
  ring

lemma flowMat_zero (ξ : Fin r → E) (τ : X.Ψ) : X.flowMat ξ τ 0 = 1 := by
  ext a b
  simp [Data.flowMat, Matrix.one_apply]

lemma det_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ) :
    (X.flowMat ξ τ s).det = 1 := by
  rw [flowMat_eq, Matrix.vecMulVec_eq Unit, ← Matrix.smul_mul, ← Matrix.replicateCol_smul,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, wv_dot_self X hξ,
    smul_zero, add_zero]

lemma flow_flow {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s s' : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s (X.flow ξ s' x) = X.flow ξ (s + s') x := by
  funext τ
  show (X.flowMat ξ τ (s τ) * (X.flowMat ξ τ (s' τ) * mat x τ) : Matrix (Fin r) (Fin r) ℂ) =
    X.flowMat ξ τ ((s + s') τ) * mat x τ
  rw [← Matrix.mul_assoc, flowMat_mul X hξ, Pi.add_apply]

lemma flow_zero (ξ : Fin r → E) (x : Frame X.Ψ r) : X.flow ξ 0 x = x := by
  funext τ
  show (X.flowMat ξ τ ((0 : X.Ψ → ℂ) τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Pi.zero_apply, flowMat_zero, Matrix.one_mul]
  rfl

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ v = v + ((-(I * X.c τ * s)) * hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) •
      Data.emb τ.1 ξ := by
  rw [flowMat_eq, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  rw [← wv_dot X ξ τ v]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end flowAlg

end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma add_conj' (w : ℂ) : w + conj w = 2 * (w.re : ℂ) := by
  apply Complex.ext <;> simp <;> ring

lemma trace_re (X : Data E r) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have hall : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
    have h' : (algebraMap ℚ ℂ) (Algebra.trace ℚ E z) = ((Algebra.trace ℚ E z : ℚ) : ℂ) :=
      eq_ratCast _ _
    rw [← h', h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
  have hconj : ∑ σ ∈ X.Ψᶜ, σ z = ∑ σ ∈ X.Ψ, conj (σ z) := by
    apply Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ)
    · intro σ hσ
      simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
      rw [X.cmType, hcc]
      exact hσ
    · intro σ hσ
      simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact hcc σ
    · intro σ _
      exact hcc σ
    · intro σ _
      simp [ComplexEmbedding.conjugate_coe_eq]
  push_cast
  rw [hall, ← Finset.sum_add_sum_compl X.Ψ, hconj, ← Finset.sum_add_distrib,
    ← Finset.sum_coe_sort X.Ψ]
  exact Finset.sum_congr rfl fun τ _ => add_conj' _

end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

section Mat

variable {n : ℕ}

lemma sub_mul_sub {i : ℕ} (h : i ≤ n) (M N : Matrix (Fin n) (Fin n) ℂ)
    (hz : ∀ (a c : Fin i) (k : Fin n), i ≤ (k : ℕ) → M (Fin.castLE h a) k * N k (Fin.castLE h c) = 0) :
    (M * N).submatrix (Fin.castLE h) (Fin.castLE h) =
      M.submatrix (Fin.castLE h) (Fin.castLE h) * N.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_) (fun k => rfl)
  apply hz a c k
  by_contra hlt
  exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩

lemma upper_lt {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) {a k : Fin n} (h : a < k) :
    N k a = 0 := hN h

lemma det_sub_upper {i : ℕ} (h : i ≤ n) {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) :
    (N.submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ j : Fin i, N (Fin.castLE h j) (Fin.castLE h j) := by
  have ht : (N.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := fun a c hca =>
    hN (show Fin.castLE h c < Fin.castLE h a from hca)
  rw [Matrix.det_of_isUpperTriangular ht]
  rfl

lemma lminor_conj {N A : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) (i : Fin (n + 1)) :
    lminor (Nᵀ * A * N.map (starRingEnd ℂ)) i =
      (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) *
        lminor A i *
        conj (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) := by
  have h := Nat.le_of_lt_succ i.isLt
  unfold lminor
  rw [sub_mul_sub h (Nᵀ * A) (N.map (starRingEnd ℂ)) (fun a c k hk => ?_),
    sub_mul_sub h Nᵀ A (fun a c k hk => ?_), Matrix.det_mul, Matrix.det_mul, ← Matrix.transpose_submatrix, Matrix.det_transpose,
    det_sub_upper h hN]
  · congr 1
    rw [show (N.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
        (starRingEnd ℂ).mapMatrix (N.submatrix (Fin.castLE h) (Fin.castLE h)) from rfl,
      ← RingHom.map_det, det_sub_upper h hN]
  all_goals
    have h1 : N k (Fin.castLE h c) = 0 :=
      upper_lt hN (show Fin.castLE h c < k by rw [Fin.lt_def]; simp; omega)
    have h2 : N k (Fin.castLE h a) = 0 :=
      upper_lt hN (show Fin.castLE h a < k by rw [Fin.lt_def]; simp; omega)
    simp [h1, h2]

end Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

@[simp] lemma cc_cc (a : E) : cc (cc a) = a := by simp [cc]
@[simp] lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by simp [cc]
@[simp] lemma cc_add (a b : E) : cc (a + b) = cc a + cc b := by simp [cc]
@[simp] lemma cc_sub (a b : E) : cc (a - b) = cc a - cc b := by simp [cc]
@[simp] lemma cc_neg (a : E) : cc (-a) = -cc a := by simp [cc]
@[simp] lemma cc_zero : cc (0 : E) = 0 := by simp [cc]
@[simp] lemma cc_one : cc (1 : E) = 1 := by simp [cc]
@[simp] lemma cc_inv (a : E) : cc a⁻¹ = (cc a)⁻¹ := by simp [cc]
lemma cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  simp [cc]
@[simp] lemma cc_eq_zero (a : E) : cc a = 0 ↔ a = 0 := by simp [cc]
@[simp] lemma cc_intCast (n : ℤ) : cc (n : E) = n := by simp [cc]
@[simp] lemma cc_natCast (n : ℕ) : cc (n : E) = n := by simp [cc]

variable {r : ℕ}

lemma herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

lemma herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x - x') y = herm G x y - herm G x' y := by
  simp [herm, sub_mul, Finset.sum_sub_distrib]

lemma herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp [herm, Finset.mul_sum, mul_assoc]

lemma herm_sub_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y - y') = herm G x y - herm G x y' := by
  simp [herm, mul_sub, Finset.sum_sub_distrib]

lemma herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_conj (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma cc_single (b c : Fin r) :
    cc ((Pi.single b (1 : E) : Fin r → E) c) = (Pi.single b (1 : E) : Fin r → E) c := by
  by_cases h : c = b
  · subst h; simp
  · simp [h]

lemma herm_single_right (G : Matrix (Fin r) (Fin r) E) (v : Fin r → E) (b : Fin r) :
    herm G v (Pi.single b 1) = (Matrix.vecMul v G) b := by
  simp only [herm, cc_single, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Pi.single_apply]

lemma eq_zero_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (v : Fin r → E)
    (hv : ∀ y, herm G v y = 0) : v = 0 := by
  apply Matrix.eq_zero_of_vecMul_eq_zero hG
  funext b
  rw [← herm_single_right]
  simpa using hv _

lemma exists_eq_smul_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hGh : ∀ a b, cc (G a b) = G b a) (ξ μ : Fin r → E) (hξ : ξ ≠ 0)
    (h : ∀ y, herm G y ξ = 0 → herm G μ y = 0) : ∃ e : E, μ = e • ξ := by
  have hk : ∃ k, herm G (Pi.single k 1) ξ ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    apply hξ
    apply Matrix.eq_zero_of_vecMul_eq_zero hG
    funext b
    rw [← herm_single_right, ← herm_conj G hGh, hne b]
    simp
  obtain ⟨k, hk⟩ := hk
  set y0 : Fin r → E := (herm G (Pi.single k 1) ξ)⁻¹ • Pi.single k 1
  have hy0 : herm G y0 ξ = 1 := by
    simp only [y0, herm_smul_left]; exact inv_mul_cancel₀ hk
  refine ⟨herm G μ y0, ?_⟩
  have hall : ∀ y, herm G (μ - herm G μ y0 • ξ) y = 0 := by
    intro y
    have h1 := h (y - herm G y ξ • y0) (by rw [herm_sub_left, herm_smul_left, hy0]; ring)
    rw [herm_sub_right, herm_smul_right, herm_conj G hGh, sub_eq_zero] at h1
    rw [herm_sub_left, herm_smul_left, h1]
    ring
  have := eq_zero_of_herm G hG _ hall
  exact sub_eq_zero.mp this

lemma eq_zero_of_trace (a : E) (h : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * a) = 0) :
    a = 0 := by
  by_contra ha
  have halg : IsAlgebraic ℤ (cc a⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  let β : 𝓞 E := ⟨y • cc a⁻¹, hint⟩
  have hβ : (β : E) = y • cc a⁻¹ := rfl
  have h1 := h β
  have h2 : cc (y • cc a⁻¹) * a = algebraMap ℚ E (y : ℚ) := by
    rw [zsmul_eq_mul, cc_mul, cc_intCast, cc_cc, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    simp
  rw [hβ, h2, Algebra.trace_algebraMap] at h1
  have hd : (Module.finrank ℚ E : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  rw [nsmul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact hd h3
  · exact hy (by exact_mod_cast h3)

theorem exists_smul_mem {R F X : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.general_b_fact_alt_form.goal1 S hx

end ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Matrix ReciprocityTheory.MultiplicativeHeights

noncomputable def d5mu (f r : ℕ) (d laStar : ℝ) : ℝ := 4 * ((f : ℝ) * r) ^ 3 * d / laStar

def CoveringRadiusStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Type) [Fintype ι] [Nonempty ι]
    (r p : ℕ) (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (laStar : ℝ),
    Function.Injective σ →
    (∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) →
    p ≤ r → 0 < laStar → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsLattice L → IsSelfDual S L →
    (∀ v ∈ L, v ≠ 0 → ∃ i, laStar ^ 2 ≤ normSq (Q i *ᵥ embVec (σ i) v)) →
    let μ := d5mu (Fintype.card ι) r |(NumberField.discr K : ℝ)| laStar
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) ∧
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ L) ∧ LinearIndependent K v ∧ ∀ j, majSq σ Q (v j) ≤ μ ^ 2

end ReciprocityTheory.ChartRestriction.G.FD
end
