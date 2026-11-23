module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramDeterminantReal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering

open Submodule Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem babai : ∀ (m : ℕ) (y : Fin m → V) (v : V), v ∈ span ℝ (Set.range y) →
    ∃ x ∈ span ℤ (Set.range y), ‖v - x‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
  have key : ∀ (m : ℕ) (y : Fin m → V) (c : Fin m → ℝ), ∃ n : Fin m → ℤ,
      ‖∑ i, (c i - (n i : ℝ)) • y i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
    intro m
    induction m with
    | zero => intro y c; exact ⟨fun i => i.elim0, by simp⟩
    | succ m ih =>
      intro y c
      obtain ⟨n, hn⟩ := ih (fun i => y i.castSucc) (fun i => c i.castSucc)
      set u := ∑ i : Fin m, (c i.castSucc - (n i : ℝ)) • y i.castSucc with hu
      set w := y (Fin.last m) with hw
      set f := Int.fract (c (Fin.last m)) with hfd
      have hf0 : 0 ≤ f := Int.fract_nonneg _
      have hf1 : f < 1 := Int.fract_lt_one _
      have havg : (1 - f) * ‖u + f • w‖ ^ 2 + f * ‖u + (f - 1) • w‖ ^ 2 =
          ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 := by
        rw [norm_add_sq_real, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_right,
          real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
        ring
      have hq : f * (1 - f) ≤ 1 / 4 := by nlinarith [sq_nonneg (f - 1 / 2)]
      have hbound : ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        have h1 := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖w‖)
        nlinarith [hn]
      have hsplit : ∀ N : ℤ, ∑ i, (c i - ((Fin.snoc (α := fun _ => ℤ) n N i : ℤ) : ℝ)) • y i =
          u + (c (Fin.last m) - (N : ℝ)) • w := by
        intro N
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, hu, hw]
      by_cases hc : ‖u + f • w‖ ^ 2 ≤ ‖u + (f - 1) • w‖ ^ 2
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n ⌊c (Fin.last m)⌋, ?_⟩
        rw [hsplit, ← Int.fract]
        nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hc)]
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n (⌊c (Fin.last m)⌋ + 1), ?_⟩
        have e : c (Fin.last m) - (((⌊c (Fin.last m)⌋ + 1 : ℤ)) : ℝ) = f - 1 := by
          rw [hfd, Int.fract]
          push_cast
          ring
        rw [hsplit, e]
        push_neg at hc
        nlinarith [mul_nonneg (sub_nonneg.mpr hf1.le) (sub_nonneg.mpr hc.le)]
  intro m y v hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  obtain ⟨n, hn⟩ := key m y c
  refine ⟨∑ i, (n i) • y i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  have e : v - ∑ i, (n i) • y i = ∑ i, (c i - (n i : ℝ)) • y i := by
    rw [← hc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, Int.cast_smul_eq_zsmul]
  rw [e]
  exact hn

theorem cover {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) (bd : ι → V)
    (hd : ∀ i j, inner ℝ (b i) (bd j) = if i = j then 1 else 0) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range bd), x ≠ 0 → lam ≤ ‖x‖) (v : V) :
    ∃ x ∈ span ℤ (Set.range b),
      ‖v - x‖ ^ 2 ≤ (finrank ℝ V : ℝ) / 4 * ((finrank ℝ V : ℝ) ^ 2 / lam) ^ 2 := by
  classical
  set n := finrank ℝ V with hn
  have hcard : Fintype.card ι = n := (finrank_eq_card_basis b).symm
  have hli : LinearIndependent ℝ bd := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (inner ℝ (b i)) hg
    simpa [inner_sum, real_inner_smul_right, hd] using this
  let Bd : Basis ι ℝ V := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  have hBd : ∀ i, Bd i = bd i := fun i => Basis.mk_apply _ _ _
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ V).repr
  let B' : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Bd.reindex e).map φ.toLinearEquiv
  have hB' : ∀ j, B' j = φ (bd (e.symm j)) := fun j => by simp [B', hBd]
  have hmin' : ∀ x ∈ span ℤ (Set.range B'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : (∑ i, c i • B' i) = φ (∑ i, c i • bd (e.symm i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [hB', map_sum, map_zsmul]
    have hwmem : (∑ i, c i • bd (e.symm i)) ∈ span ℤ (Set.range bd) :=
      sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self _)) _
    rw [hw, LinearIsometryEquiv.norm_map]
    refine hmin _ hwmem ?_
    intro h0
    apply hx0
    rw [hw, h0, map_zero]
  obtain ⟨y, hyli, hyint, hynorm⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual B' lam hlam hmin'
  let yV : Fin n → V := fun i => φ.symm (y i)
  have hyVint : ∀ i k, ∃ m : ℤ, inner ℝ (yV i) (bd k) = m := by
    intro i k
    obtain ⟨m, hm⟩ := hyint i (e k)
    refine ⟨m, ?_⟩
    rw [← hm, hB', Equiv.symm_apply_apply, ← LinearIsometryEquiv.inner_map_map φ]
    simp [yV]
  have hyVmem : ∀ i, yV i ∈ span ℤ (Set.range b) := by
    intro i
    have hrep : ∀ k, b.repr (yV i) k = inner ℝ (yV i) (bd k) := by
      intro k
      have h : inner ℝ (yV i) (bd k) = ∑ l, b.repr (yV i) l * inner ℝ (b l) (bd k) := by
        conv_lhs => rw [← b.sum_repr (yV i)]
        rw [sum_inner]
        simp_rw [real_inner_smul_left]
      rw [h]
      simp [hd]
    rw [← b.sum_repr (yV i)]
    refine sum_mem fun k _ => ?_
    obtain ⟨m, hm⟩ := hyVint i k
    rw [hrep, hm, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (subset_span (Set.mem_range_self k)) m
  have hyVli : LinearIndependent ℝ yV :=
    hyli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker
  have hspan : span ℝ (Set.range yV) = ⊤ :=
    hyVli.span_eq_top_of_card_eq_finrank' (by simp [n])
  obtain ⟨x, hx, hxb⟩ := babai n yV v (hspan ▸ mem_top)
  refine ⟨x, span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyVmem i) hx, hxb.trans ?_⟩
  calc (1 / 4) * ∑ i, ‖yV i‖ ^ 2 ≤ (1 / 4) * ∑ _i : Fin n, ((n : ℝ) ^ 2 / lam) ^ 2 := by
        gcongr with i
        have : ‖yV i‖ = ‖y i‖ := by simp [yV]
        rw [this]
        exact hynorm i
    _ = (n : ℝ) / 4 * ((n : ℝ) ^ 2 / lam) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section gram

variable (X : Data E r)

def hv (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Fin r → ℂ :=
  fun a => hermC τ.1 X.Gm (col M a) (Data.emb τ.1 ξ)

def rk1 (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  vecMulVec (hv X ξ τ M) (fun b => conj (hv X ξ τ M b))

lemma col_mul (A M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * M) a = A *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private lemma hermC_add_smul_add_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u e v : Fin r → ℂ)
    (β γ : ℂ) :
    hermC τ G (u + β • e) (v + γ • e) = hermC τ G u v + conj γ * hermC τ G u e +
      β * hermC τ G e v + β * conj γ * hermC τ G e e := by
  simp only [hermC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma hermC_swap_of_conj_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by

  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc', hG]
  ring

lemma hermC_pair (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (e u v : Fin r → ℂ) (he : hermC τ G e e = 0) (α : ℂ) :
    hermC τ G (u + (α * hermC τ G u e) • e) (v + (α * hermC τ G v e) • e) =
      hermC τ G u v + (α + conj α) * hermC τ G u e * conj (hermC τ G v e) := by
  rw [hermC_add_smul_add_smul, hermC_swap_of_conj_symm τ G hG v e, he]
  simp only [map_mul]
  ring

lemma alpha_conj (c : ℝ) (s : ℂ) :
    (-(I * (c : ℂ) * s)) + conj (-(I * (c : ℂ) * s)) = ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private lemma hermC_emb_emb_eq_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by

  simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc']

lemma gram_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.flowMat ξ τ s * M) =
      gram τ.1 X.Gm M + ((2 * X.c τ * s.im : ℝ) : ℂ) • rk1 X ξ τ M := by
  have he : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_herm, hξ, map_zero]
  ext a b
  simp only [gram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rk1, hv,
    vecMulVec_apply]
  rw [col_mul, col_mul, flowMat_mulVec (X := X), flowMat_mulVec (X := X),
    hermC_pair τ.1 X.Gm X.Gm_herm _ _ _ he, alpha_conj]
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

def admissibleImaginary (ξ : Fin r → E) (x : Frame X.Ψ r) : Set (X.Ψ → ℝ) :=
  {y | ∀ τ : X.Ψ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i *
    (lminor (gram τ.1 X.Gm (mat x τ) + ((2 * X.c τ * y τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re}

lemma flow_mem_dom_iff {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) :
    X.flow ξ s x ∈ X.dom ↔ (fun τ => (s τ).im) ∈ admissibleImaginary X ξ x := by
  simp only [Data.dom, GG, Set.mem_setOf_eq, admissibleImaginary, dmin, mat_flow, gram_flowMat X hξ, det_mul,
    det_flowMat (X := X) hξ, one_mul]
  constructor
  · intro h τ i
    exact (h τ).2 i
  · intro h τ
    exact ⟨(hx τ).1, h τ⟩

end gram

section affine

lemma leadingMinor_add_rankOne (A : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) (i : Fin (r + 1))
    (hA : lminor A i ≠ 0) : ∃ κ : ℂ, ∀ t : ℂ, lminor (A + t • vecMulVec u v) i = lminor A i * (1 + t * κ) := by
  unfold lminor at hA ⊢
  set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  set B := A.submatrix e e with hB
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨(v ∘ e) ⬝ᵥ (B⁻¹ *ᵥ (u ∘ e)), fun t => ?_⟩
  have hz : B *ᵥ (B⁻¹ *ᵥ (u ∘ e)) = u ∘ e := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hB', one_mulVec]
  have key : B * (1 + vecMulVec (B⁻¹ *ᵥ (u ∘ e)) (t • (v ∘ e))) =
      (A + t • vecMulVec u v).submatrix e e := by
    rw [mul_add, mul_one]
    ext a b
    have hza : ∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k = u (e a) := congrFun hz a
    simp only [Matrix.add_apply, Matrix.mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    rw [show ∑ k, B a k * ((B⁻¹ *ᵥ (u ∘ e)) k * (t * v (e b))) =
        (∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k) * (t * v (e b)) by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring, hza]
    simp only [hB, Matrix.submatrix_apply]
    ring
  rw [← key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
    smul_eq_mul]

lemma open_convex_aff {ι κ : Type*} [Fintype ι] [Finite κ] (a b : ι → κ → ℝ) :
    IsOpen {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} ∧
      Convex ℝ {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  constructor
  · have hs : {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} =
        ⋂ τ, ⋂ i, {y : ι → ℝ | 0 < a τ i + y τ * b τ i} := by
      ext y
      simp
    rw [hs]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_const.add ((continuous_apply τ).mul continuous_const))
  · intro y hy z hz s t hs ht hst
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hz ⊢
    intro τ i
    have h1 := hy τ i
    have h2 := hz τ i
    have key : a τ i + (s * y τ + t * z τ) * b τ i =
        s * (a τ i + y τ * b τ i) + t * (a τ i + z τ * b τ i) := by
      linear_combination (-(a τ i)) * hst
    rw [key]
    rcases hs.lt_or_eq with hs' | hs'
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' h1) (mul_nonneg ht h2.le)
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using h2

end affine

section adm

variable (X : Data E r)

lemma admissibleImaginary_eq_halfspaces {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    ∃ a b : X.Ψ → Fin (r + 1) → ℝ, admissibleImaginary X ξ x = {y | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  have hL : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), lminor (gram τ.1 X.Gm (mat x τ)) i ≠ 0 := by
    intro τ i h
    have h1 := (hx τ).2 i
    simp only [dmin, h, Complex.zero_re, mul_zero, lt_irrefl] at h1
  have hk : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), ∃ κ : ℂ, ∀ t : ℂ,
      lminor (gram τ.1 X.Gm (mat x τ) + t • rk1 X ξ τ (mat x τ)) i =
        lminor (gram τ.1 X.Gm (mat x τ)) i * (1 + t * κ) :=
    fun τ i => leadingMinor_add_rankOne _ _ _ i (hL τ i)
  choose κ hκ using hk
  have hre : ∀ (L k : ℂ) (t : ℝ), (L * (1 + (t : ℂ) * k)).re = L.re + t * (L * k).re := by
    intro L k t
    rw [show L * (1 + (t : ℂ) * k) = L + (t : ℂ) * (L * k) by ring, Complex.add_re,
      Complex.re_ofReal_mul]
  refine ⟨fun τ i => psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ)) i).re,
    fun τ i => psgn X.p0 i * (2 * X.c τ) * (lminor (gram τ.1 X.Gm (mat x τ)) i * κ τ i).re, ?_⟩
  ext y
  simp only [admissibleImaginary, Set.mem_setOf_eq, hκ, hre]
  refine forall_congr' fun τ => forall_congr' fun i => ?_
  apply iff_of_eq
  congr 1
  ring

lemma admissibleImaginary_open_convex {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    IsOpen (admissibleImaginary X ξ x) ∧ Convex ℝ (admissibleImaginary X ξ x) := by
  obtain ⟨a, b, h⟩ := admissibleImaginary_eq_halfspaces X (ξ := ξ) x hx
  rw [h]
  exact open_convex_aff a b

end adm

end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}

def flw (α : ℂ) (e : Fin r → ℂ) (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (f : Fin n → Fin r → ℂ) : Fin n → Fin r → ℂ :=
  fun a => f a + (α * hermC τ G (f a) e) • e

theorem cv_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    cv τ G (flw α e τ G f) e = cv τ G f e := by
  funext a
  show hermC τ G e (f a + (α * hermC τ G (f a) e) • e) = hermC τ G e (f a)
  rw [GramDeterminantReal.hC_add_right, GramDeterminantReal.hermC_smul_right, he, mul_zero, add_zero]
  all_goals exact hG

theorem gramF_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    gramF τ G (flw α e τ G f) = gramF τ G f +
      replicateCol Unit (fun a => (α + conj α) * conj (cv τ G f e a)) *
        replicateRow Unit (cv τ G f e) := by
  ext a b
  have hc := GramDeterminantReal.hC_conj hG
  simp only [Matrix.add_apply, Matrix.mul_apply, replicateCol, replicateRow, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.gramF, flw]
  rw [GramDeterminantReal.hC_add_left, GramDeterminantReal.hC_add_right, GramDeterminantReal.hC_add_right,
    GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_right,
    GramDeterminantReal.hermC_smul_right, he, hc e (f a)]
  all_goals try exact hG
  simp only [GramDeterminantReal.cv, map_mul]
  rw [← hc (f b) e]
  ring

theorem mt_y {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    GramDeterminantReal.mt τ G f e = ∑ b, yv τ G f e b * conj (cv τ G f e b) := by
  simp only [GramDeterminantReal.mt, GramDeterminantReal.yv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) : (gramF τ G (flw α e τ G f)).det =
      (gramF τ G f).det * (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  rw [gramF_flw hG e he α f, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateCol, replicateRow,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.mt, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mt_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) (h1 : 1 + (α + conj α) * GramDeterminantReal.mt τ G f e ≠ 0) :
    GramDeterminantReal.mt τ G (flw α e τ G f) e =
      GramDeterminantReal.mt τ G f e / (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  set s := α + conj α with hs
  set m := GramDeterminantReal.mt τ G f e with hm
  have hA' : IsUnit (gramF τ G (flw α e τ G f)).det := by
    rw [det_flw hG e he α f hA]
    exact hA.mul (isUnit_iff_ne_zero.mpr h1)
  have hyA : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e := by
    simp only [GramDeterminantReal.yv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  have hyB : Matrix.vecMul (yv τ G f e)
      (replicateCol Unit (fun a => s * conj (cv τ G f e a)) * replicateRow Unit (cv τ G f e)) =
      (s * m) • cv τ G f e := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, replicateCol, replicateRow,
      Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul]
    rw [hm, mt_y, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key : Matrix.vecMul (yv τ G f e) (gramF τ G (flw α e τ G f)) =
      (1 + s * m) • cv τ G f e := by
    rw [gramF_flw hG e he α f, Matrix.vecMul_add, hyA, hyB, add_smul, one_smul]
  have hy : yv τ G (flw α e τ G f) e = (1 + s * m)⁻¹ • yv τ G f e := by
    have h2 : yv τ G f e = (1 + s * m) • yv τ G (flw α e τ G f) e := by
      conv_rhs => rw [GramDeterminantReal.yv, cv_flw hG e he α f, ← Matrix.smul_vecMul, ← key,
        Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA', Matrix.vecMul_one]
    rw [h2, smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [mt_y (flw α e τ G f) e, hy, cv_flw hG e he α f, div_eq_inv_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  congr 1
  exact (mt_y f e).symm

end

end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
end
