module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section herm

variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

lemma hC_add_left (u u' v : Fin r → ℂ) : hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma hC_sub_left (u u' v : Fin r → ℂ) : hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma hC_smul_left (c : ℂ) (u v : Fin r → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_add_right (u v v' : Fin r → ℂ) : hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

lemma hC_smul_right (c : ℂ) (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ G (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hC_add_left, ih]

lemma hC_symm (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by

  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc, hG]
  ring

lemma emb_herm (x y : Fin r → E) : τ (herm G x y) = hermC τ G (Data.emb τ x) (Data.emb τ y) := by

  simp only [herm, hermC, Data.emb, map_sum, map_mul, emb_cc]

end herm

namespace Data

variable {r : ℕ} (X : Data E r)

lemma col_mul (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * B) a = Matrix.mulVec A (col B a) := by
  funext k; simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  funext a
  simp only [flowMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, emb, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

lemma ppos_eq_of (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (β : Fin X.p0 → ℂ)
    (horth : ∀ b : Fin X.p0, hermC τ.1 X.Gm (u - ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) :
    X.ppos x τ u = ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a) := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have hc : cf = Matrix.vecMul β A := by
    funext b
    have h := horth b
    rw [hC_sub_left, sub_eq_zero, hC_sum_left] at h
    simp only [cf, h, hC_smul_left, Matrix.vecMul, dotProduct, hAdef, gramPos, gram,
      Matrix.submatrix_apply, Matrix.of_apply]
  have hα : (fun a => ∑ b, cf b * A⁻¹ b a) = β := by
    have : Matrix.vecMul cf A⁻¹ = β := by
      rw [hc, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.vecMul_one]
    rw [← this]; rfl
  unfold ppos
  rw [← hα]

lemma ppos_orth (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (b : Fin X.p0) : hermC τ.1 X.Gm (u - X.ppos x τ u) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have key : Matrix.vecMul (Matrix.vecMul cf A⁻¹) A = cf := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hA), Matrix.vecMul_one]
  have h2 := congrFun key b
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [hC_sub_left, sub_eq_zero]
  unfold ppos
  rw [hC_sum_left]
  simp only [hC_smul_left]
  rw [show hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) = cf b from rfl, ← h2]
  rfl

lemma gramPos_det_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : (X.gramPos x τ).det ≠ 0 := by
  have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
  intro h0
  have : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
  rw [this] at h
  simp at h

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis

open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev CP := {w : InfinitePlace E // IsComplex w}

abbrev VS := EuclideanSpace ℂ (CP E)

instance isEmpty_real : IsEmpty {w : InfinitePlace E // IsReal w} :=
  ⟨fun w => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩

noncomputable def iota : E →+ VS E where
  toFun x := WithLp.toLp 2 (fun w : CP E => w.1.embedding x)
  map_zero' := by ext w; simp
  map_add' x y := by ext w; simp

variable {E}

lemma iota_apply (x : E) (w : CP E) : iota E x w = w.1.embedding x := rfl

lemma conj_conj (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  first
    | exact ComplexEmbedding.conjugate_conjugate φ
    | (ext x; simp [ComplexEmbedding.conjugate_coe_eq])

lemma inner_iota (x y : E) :
    inner ℝ (iota E x) (iota E y) = ∑ w : CP E, (w.1.embedding x * conj (w.1.embedding y)).re := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [iota_apply, iota_apply, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma norm_sq_iota (x : E) : ‖iota E x‖ ^ 2 = ∑ w : CP E, ‖w.1.embedding x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [iota_apply]

lemma sum_re_eq_trace (u : E) :
    ∑ w : CP E, (w.1.embedding u).re = (1 / 2 : ℝ) * (Algebra.trace ℚ E u : ℝ) := by
  have hall : ∀ w : InfinitePlace E, IsComplex w := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mp fun hw =>
      IsEmpty.false (⟨w, hw⟩ : {w : InfinitePlace E // IsReal w})
  have hfib : ∀ w : InfinitePlace E,
      ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ u =
        w.embedding u + conj (w.embedding u) := by
    intro w
    have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hall w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
    have hset : Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
          rw [h, InfinitePlace.mk_embedding]
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h1
        · exact Or.inl h1
        · right
          rw [← h1, conj_conj]
      · rintro (rfl | rfl)
        · exact InfinitePlace.mk_embedding w
        · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [hset, Finset.sum_pair hne.symm, ComplexEmbedding.conjugate_coe_eq]
  have h0 : algebraMap ℚ ℂ (Algebra.trace ℚ E u) = ∑ σ : E →ₐ[ℚ] ℂ, σ u := by
    first
      | exact trace_eq_sum_embeddings ℂ
      | exact trace_eq_sum_embeddings ℂ (x := u)
      | exact trace_eq_sum_embeddings (E := ℂ) (x := u)
      | exact Algebra.trace_eq_sum_embeddings ℂ
  have h1 : ∑ σ : E →ₐ[ℚ] ℂ, σ u = ∑ φ : E →+* ℂ, φ u :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ u)
      (fun σ : E →ₐ[ℚ] ℂ => σ u)
      (fun _ => rfl)).symm
  have h2 : ∑ φ : E →+* ℂ, φ u =
      ∑ w : InfinitePlace E, (w.embedding u + conj (w.embedding u)) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ u)]
    refine Finset.sum_congr rfl fun w _ => ?_
    first
      | exact hfib w
      | convert hfib w
  have h3 : ((Algebra.trace ℚ E u : ℚ) : ℂ) =
      ∑ w : CP E, (w.1.embedding u + conj (w.1.embedding u)) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), h0, h1, h2]
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv hall) _ _ (fun _ => rfl)).symm
  have h4 := congrArg Complex.re h3
  rw [Complex.re_sum] at h4
  simp only [Complex.add_re, Complex.conj_re, Complex.ratCast_re] at h4
  rw [h4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

variable (E)

noncomputable def toVS : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] VS E :=
  LinearEquiv.ofLinearMap
    (f := (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).symm.toLinearMap ∘ₗ LinearMap.snd ℝ _ _)
    (g := LinearMap.inr ℝ _ _ ∘ₗ (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).toLinearMap)
    (by ext z w; simp)
    (by
      apply LinearMap.ext
      intro z
      refine Prod.ext (funext fun w => (IsEmpty.false w).elim) ?_
      simp)

noncomputable def bas : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (VS E) :=
  (mixedEmbedding.latticeBasis E).map (toVS E)

variable {E}

lemma bas_apply (i : Free.ChooseBasisIndex ℤ (𝓞 E)) : bas E i = iota E (integralBasis E i) := by
  rw [bas, Basis.map_apply, mixedEmbedding.latticeBasis_apply]
  first
    | rfl
    | (ext w; simp [toVS, iota, mixedEmbedding])

lemma mem_span_bas {x : VS E} (hx : x ∈ span ℤ (Set.range (bas E))) :
    ∃ α : 𝓞 E, x = iota E (α : E) := by
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨∑ i, c i • RingOfIntegers.basis E i, ?_⟩

  simp only [bas_apply, integralBasis_apply, ← map_zsmul, ← map_sum]

lemma card_CP : Fintype.card (CP E) = fdeg E ∧ finrank ℚ E = 2 * Fintype.card (CP E) := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h0 : nrRealPlaces E = 0 := by
    first
      | exact Fintype.card_eq_zero
      | simp [nrRealPlaces]
  have h1 : nrComplexPlaces E = Fintype.card (CP E) := rfl
  rw [h0, zero_add, h1] at h
  refine ⟨?_, h.symm⟩
  unfold fdeg
  rw [← h]
  omega

lemma finrank_VS : finrank ℝ (VS E) = finrank ℚ E := by
  rw [← (toVS E).finrank_eq]
  first
    | exact mixedEmbedding.finrank E
    | exact mixedEmbedding.finrank

end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma hermC_sub_left_of_ringHom (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma ppos_sub (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  simp only [Data.ppos, hermC_sub_left_of_ringHom, sub_mul, Finset.sum_sub_distrib, sub_smul]

variable {X : Data E r}

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def IsOrtho (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

abbrev Coord : Type := X.Ψ → Fin (r - X.p0) → Fin X.p0 → ℂ

def lowBlock (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    if h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
      Z τ ⟨(a : ℕ) - X.p0, by have := a.isLt; omega⟩ ⟨b, h.2⟩ else 0

def xZ (x : Frame X.Ψ r) (Z : X.Coord) : Frame X.Ψ r :=
  fun τ => (mat x τ * X.lowBlock Z τ : Matrix (Fin r) (Fin r) ℂ)

def opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
    t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)}

def zN (Z : X.Coord) : ℝ := ⨆ τ : X.Ψ, opN (Matrix.of (Z τ))

end Data

def OrthonormalFlagTranslate : Prop :=
  ∀ (r : ℕ) (X : Data E r),
    (∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, X.IsOrtho (rmul x b)) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) →
      ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.pnorm la P (rmul x b) = X.pnorm la P x) ∧
    ∀ x ∈ X.dom, ∀ x' ∈ X.dom, X.SameFlag x x' → (∀ ξ : Fin r → E,
      X.Jz x = X.Jz x' ∧ X.Uz x ξ = X.Uz x' ξ ∧ X.aproj x ξ = X.aproj x' ξ) ∧ X.maj x = X.maj x'

def OrthonormalChartNormControl : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), x ∈ X.dom → X.IsOrtho x → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 10 →
    (∀ Z : X.Coord, X.zN Z ≤ ρ →
      X.xZ x Z ∈ X.dom ∧
      (∀ (la : Wt X.Ψ r) (w : ℝ), (∑ τ, X.spread la τ) ≤ w →
        |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2) ∧
      ∀ τ v, (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
        X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v) ∧
    ∀ G : Frame X.Ψ r → ℂ, DifferentiableOn ℂ G X.dom →
      DifferentiableOn ℂ (fun Z : X.Coord => G (X.xZ x Z)) {Z | X.zN Z < ρ}

def NearSupremumTransference : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x' ∈ X.dom, (∀ τ, (1 - d6rh c1 w) / (1 + d6rh c1 w) ≤ X.tt ξ x' τ ∧
      X.tt ξ x' τ ≤ (1 + d6rh c1 w) / (1 - d6rh c1 w)) →
    X.hatN la (X.fj la ξ ν P) x' ≤
      Real.exp 2 * sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}

def SchwarzLemmaBall : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (γ : V → ℂ) (ρ S : ℝ), 0 < ρ →
    DifferentiableOn ℂ γ (closedBall 0 ρ) → (∀ Z ∈ closedBall (0 : V) ρ, ‖γ Z‖ ≤ Real.exp (9 / 4) * S) →
    S / 2 < ‖γ 0‖ → ‖γ 0‖ ≤ S → ∀ Z ∈ ball (0 : V) (ρ / 21), γ Z ≠ 0

def SplitData {r : ℕ} (X : DataX E r) (ξ : Fin r → E) (La : ℝ) (z : Frame X.Ψ r)
    (lam : Fin (r - 2) → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
  LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
  (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = I • X.ucomp z ξ (X.embV (lam j))) ∧
  (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = -(I • X.ucomp z ξ (X.embV (lam j)))) ∧
  ∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2

def OrthonormalShortVectorBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∃ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam ∧
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) ∧ X.zN Z1 ≤ d6rh c1 w / 100

def IsotropicCoefficientSplitting : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∃ f : (Fin r → E) → E, (∀ μ ∈ X.Λp ξ, f μ • ξ ∈ X.Λ) ∧
      (∀ μ ∈ X.Λp ξ, ∀ μ' ∈ X.Λp ξ, f (μ + μ') = f μ + f μ') ∧
      (∀ (α : 𝓞 E), ∀ μ ∈ X.Λp ξ, f ((α : E) • μ) = α * f μ) ∧
      ∀ e : E, e • ξ ∈ X.Λ → f (e • ξ) = e

def NoShortVectorLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (ep0 : ℝ), X.IsIso ξ → 0 < ep0 → ∀ z ∈ X.FramesOverBasis ξ,
    (∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep0 ≤ X.maj z τ (X.ucomp z ξ (X.embV x) τ)) →
    ∀ δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ, ∃ μ ∈ X.Λp ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      X.maj z τ ((δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV μ) τ)) • Data.emb τ.1 ξ) ≤
        frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ)

def UnitaryUnipotentMove : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∀ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 →
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) →
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) →
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam →
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) → X.zN Z1 ≤ d6rh c1 w / 100 →
      ∀ n' : ℕ, 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC
          (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) / d6rh c1 w ≤ n' →
      ∃ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z : X.Coord),
        X.IsUnitaryC n ∧ (∀ τ, Matrix.mulVec (n τ) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ) ∧
        (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧
          (n' : ℂ) • X.aproj (X.lmulC n (X.lmulC h1 z0)) ξ (X.embV μ) = X.embV (e • ξ)) ∧
        SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w)
          (d6rh c1 w)) (X.lmulC n (X.lmulC h1 z0)) lam ∧
        X.SameFlag (X.lmulC n (X.lmulC h1 z0)) (X.xZ x0 Z) ∧ X.zN Z < d6rh c1 w / 21

end

end ReciprocityTheory.ChartRestriction.G.FD
end
