module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpSpanRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.TubeSummability

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexConjugate

lemma summable_exp_abs (c : ℝ) (hc : 0 < c) :
    ∀ n : ℕ, Summable (fun k : Fin n → ℤ => Real.exp (-c * ∑ j, |(k j : ℝ)|)) := by
  have hgeo : Summable (fun m : ℕ => Real.exp (-c) ^ m) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using Real.exp_lt_exp.2 (by linarith : -c < 0))
  have h1 : Summable (fun m : ℤ => Real.exp (-c * |(m : ℝ)|)) := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun m => ?_
      simp only [Function.comp, Int.cast_natCast, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
    · refine hgeo.congr fun m => ?_
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    convert h1.mul_of_nonneg ih (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) using 1
    funext p
    simp [Fin.consEquiv, Fin.sum_univ_succ, mul_add, Real.exp_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section line

variable (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r)
  {n : ℕ} (ω : Fin n → X.Ψ → ℝ)

def Lc (t : Fin n → ℂ) : X.Ψ → ℂ := fun τ => ∑ j, t j * (ω j τ : ℂ)

noncomputable def hline (t : Fin n → ℂ) : ℂ := P (X.flow ξ (Lc X ω t) x)

def Om : Set (Fin n → ℝ) := (Fintype.linearCombination ℝ ω) ⁻¹' admissibleImaginary X ξ x

lemma lincomb_apply (y : Fin n → ℝ) (τ : X.Ψ) :
    Fintype.linearCombination ℝ ω y τ = ∑ j, y j * ω j τ := by
  simp [Fintype.linearCombination_apply, Finset.sum_apply]

lemma Lc_im (t : Fin n → ℂ) :
    (fun τ => (Lc X ω t τ).im) = Fintype.linearCombination ℝ ω (fun j => (t j).im) := by
  funext τ
  rw [lincomb_apply]
  simp [Lc, Complex.im_sum]

variable {X ξ x}

lemma flow_Lc_mem_dom (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) (t : Fin n → ℂ) :
    X.flow ξ (Lc X ω t) x ∈ X.dom ↔ t ∈ tube n (Om X ξ x ω) := by
  rw [flow_mem_dom_iff (X := X) hξ x hx, Lc_im]
  rfl

lemma Om_open_convex (hx : x ∈ X.dom) : IsOpen (Om X ξ x ω) ∧ Convex ℝ (Om X ξ x ω) := by
  have hc : Continuous (Fintype.linearCombination ℝ ω) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ho, hcv⟩ := admissibleImaginary_open_convex (X := X) (ξ := ξ) x hx
  exact ⟨ho.preimage hc, hcv.linear_preimage _⟩

lemma zero_mem_Om (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) : (0 : Fin n → ℝ) ∈ Om X ξ x ω := by
  have h0 := (flow_mem_dom_iff (X := X) hξ x hx 0).1 (by rw [flow_zero]; exact hx)
  show Fintype.linearCombination ℝ ω 0 ∈ admissibleImaginary X ξ x
  rw [map_zero]
  simp only [Pi.zero_apply, Complex.zero_im] at h0
  exact h0

variable (X ξ x)

lemma hline_diff (hP : X.IsSec la P) (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) :
    DifferentiableOn ℂ (hline X P ξ x ω) (tube n (Om X ξ x ω)) := by
  intro t ht
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hLc : Differentiable ℂ (fun t : Fin n → ℂ => Lc X ω t) :=
    differentiable_pi.2 fun τ => Differentiable.fun_sum fun j _ =>
      (differentiable_apply j).mul_const _
  have hd1 : DifferentiableAt ℂ (fun t => X.flow ξ (Lc X ω t) x) t :=
    (flow_differentiable X ξ x).differentiableAt.comp t (hLc t)
  exact (hP.1 _ hmem).comp t hd1.differentiableWithinAt
    (fun t' ht' => (flow_Lc_mem_dom ω hξ hx t').2 ht')

lemma hline_periodic (hP : X.IsSec la P) (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0)
    (hx : x ∈ X.dom) (hωp : ∀ j, ω j ∈ X.periods la) :
    ∀ t ∈ tube n (Om X ξ x ω), ∀ m : Fin n → ℤ,
      hline X P ξ x ω (t + fun j => (m j : ℂ)) = hline X P ξ x ω t := by
  intro t ht m
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hp : (∑ j, (m j : ℝ) • ω j) ∈ X.periods la :=
    sum_mem fun j _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hωp j) _
  have hLc : Lc X ω (t + fun j => (m j : ℂ)) = cR X (∑ j, (m j : ℝ) • ω j) + Lc X ω t := by
    funext τ
    simp [Lc, cR, add_mul, Finset.sum_add_distrib, Finset.sum_apply, add_comm]
  simp only [hline]
  rw [hLc, ← flow_flow X hξ]
  exact sec_periodic X la P hP hξΛ hξ hp _ hmem

end line

end ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)

def eps (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1

def Mmat : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    ∑ k, (eps p k * (g k - f k) a) * ∑ m, τ (G b m) * conj (f k m)

theorem eps_sq (k : Fin n) : eps p k * eps p k = 1 := by
  unfold eps
  split_ifs <;> norm_num

theorem Mmat_mulVec (v : Fin r → ℂ) :
    Mmat τ G p f g *ᵥ v = v + ∑ k, (eps p k * hermC τ G v (f k)) • (g k - f k) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hermC, Pi.sub_apply]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
  ring

private lemma hermC_add_left' (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma hermC_add_right_fundamental_domains' (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  unfold hermC
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

private lemma hermC_sum_smul_left {m : ℕ} (c : Fin m → ℂ) (q : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ k, c k • q k) v = ∑ k, c k * hermC τ G (q k) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * q k a * τ (G a b) * conj (v b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * q k a * τ (G a b) * conj (v b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

private lemma hermC_sum_smul_right {m : ℕ} (u : Fin r → ℂ) (d : Fin m → ℂ) (q : Fin m → Fin r → ℂ) :
    hermC τ G u (∑ l, d l • q l) = ∑ l, conj (d l) * hermC τ G u (q l) := by
  unfold hermC

  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

theorem expand (q : Fin n → Fin r → ℂ) (x y : Fin r → ℂ) (c d : Fin n → ℂ)
    (hx : ∀ l, hermC τ G x (q l) = 0) (hy : ∀ k, hermC τ G (q k) y = 0) :
    hermC τ G (x + ∑ k, c k • q k) (y + ∑ l, d l • q l) =
      hermC τ G x y + ∑ k, ∑ l, c k * conj (d l) * hermC τ G (q k) (q l) := by
  rw [hermC_add_left', hermC_add_right_fundamental_domains', hermC_add_right_fundamental_domains']
  simp only [hermC_sum_smul_right, hermC_sum_smul_left, hx, hy, mul_zero, Finset.sum_const_zero, add_zero,
    Finset.mul_sum]
  rw [zero_add, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf

theorem hf_eps (k l : Fin n) : hermC τ G (f k) (f l) = if k = l then eps p k else 0 := by
  rw [hf]
  rfl

theorem Mmat_f (l : Fin n) : Mmat τ G p f g *ᵥ f l = g l := by
  rw [Mmat_mulVec]
  simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, eps_sq, one_smul]
  abel

theorem Mmat_fix (v : Fin r → ℂ) (hv : ∀ k, hermC τ G v (f k) = 0) : Mmat τ G p f g *ᵥ v = v := by
  rw [Mmat_mulVec]
  simp [hv]

theorem Mmat_comb (β : Fin n → ℂ) : Mmat τ G p f g *ᵥ (∑ c, β c • f c) = ∑ c, β c • g c := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, Mmat_f τ G p f g hG hf]

private lemma hermC_eq_conj_hermC_swap (u v : Fin r → ℂ) : hermC τ G u v = conj (hermC τ G v u) := by
  unfold hermC

  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hG i j]
  simp only [cc, IsCMField.complexEmbedding_complexConj]
  ring

theorem Mmat_unitary (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f))
    (hg : ∀ k l, hermC τ G (g k) (g l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (v w : Fin r → ℂ) :
    hermC τ G (Mmat τ G p f g *ᵥ v) (Mmat τ G p f g *ᵥ w) = hermC τ G v w := by
  have hconj : ∀ u u', hermC τ G u u' = conj (hermC τ G u' u) := hermC_eq_conj_hermC_swap τ G p f hG hf
  have hdec : ∀ u : Fin r → ℂ, ∃ (x : Fin r → ℂ) (cu : Fin n → ℂ),
      u = x + ∑ k, cu k • f k ∧ ∀ l, hermC τ G x (f l) = 0 := by
    intro u
    refine ⟨u + ∑ k, (-(eps p k * hermC τ G u (f k))) • f k, fun k => eps p k * hermC τ G u (f k), ?_,
      fun l => ?_⟩
    · simp only [neg_smul, Finset.sum_neg_distrib]
      abel
    · rw [hermC_add_left', hermC_sum_smul_left]
      simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linear_combination (-hermC τ G u (f l)) * eps_sq p l
  have hperp : ∀ x : Fin r → ℂ, (∀ l, hermC τ G x (f l) = 0) → ∀ k, hermC τ G x (g k) = 0 := by
    intro x hx k
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hgf k)
    rw [← ha, hermC_sum_smul_right]
    simp [hx]
  obtain ⟨xv, cv, hv, hxv⟩ := hdec v
  obtain ⟨xw, cw, hw, hxw⟩ := hdec w
  have hMv : Mmat τ G p f g *ᵥ v = xv + ∑ k, cv k • g k := by
    rw [hv, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xv hxv, Mmat_comb τ G p f g hG hf]
  have hMw : Mmat τ G p f g *ᵥ w = xw + ∑ k, cw k • g k := by
    rw [hw, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xw hxw, Mmat_comb τ G p f g hG hf]
  rw [hMv, hMw, hv, hw]
  rw [expand τ G g xv xw cv cw (hperp xv hxv) (fun k => by rw [hconj, hperp xw hxw k, map_zero]),
    expand τ G f xv xw cv cw hxv (fun k => by rw [hconj, hxw k, map_zero])]
  simp only [hg, hf]

theorem Mmat_span (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f)) (v : Fin r → ℂ)
    (hv : v ∈ Submodule.span ℂ (Set.range f)) :
    Mmat τ G p f g *ᵥ v ∈ Submodule.span ℂ (Set.range f) := by
  rw [Mmat_mulVec]
  exact Submodule.add_mem _ hv (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.sub_mem _ (hgf k) (Submodule.subset_span ⟨k, rfl⟩)))

end

end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation

open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

theorem pack {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (μ : Measure W) [μ.IsAddHaarMeasure]
    (S : Finset W) (R : ℝ) (hR : 0 ≤ R) (hS : ∀ p ∈ S, ‖p‖ ≤ R)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) :
    (S.card : ℝ) ≤ (1 + 2 * R) ^ finrank ℝ W := by
  set d := finrank ℝ W
  have hdisj : (S : Set W).PairwiseDisjoint fun p => ball p (1 / 2) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    rw [mem_ball, dist_eq_norm] at hzp hzq
    have h1 := hsep p hp q hq hpq
    have h2 : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
      calc ‖p - q‖ = ‖(z - q) - (z - p)‖ := by congr 1; abel
        _ ≤ ‖z - q‖ + ‖z - p‖ := norm_sub_le _ _
        _ = ‖z - p‖ + ‖z - q‖ := add_comm _ _
    linarith
  have hsub : (⋃ p ∈ S, ball p (1 / 2)) ⊆ ball (0 : W) (R + 1 / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, mem_ball, dist_eq_norm] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    calc ‖z‖ = ‖(z - p) + p‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le _ _
      _ < 1 / 2 + R := by linarith [hS p hp]
      _ = R + 1 / 2 := add_comm _ _
  have h := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at h
  simp only [Measure.addHaar_ball μ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Measure.addHaar_ball μ _ (by positivity : (0 : ℝ) ≤ R + 1 / 2), Finset.sum_const,
    nsmul_eq_mul] at h
  rw [← mul_assoc] at h
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hctop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hctop).mp h
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 : (S.card : ℝ) = (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [h3]
  calc (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d ≤ (R + 1 / 2) ^ d * 2 ^ d :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (1 + 2 * R) ^ d := by
        rw [← mul_pow]
        congr 1
        ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma one_le_abs_norm (γ : 𝓞 E) (hγ : γ ≠ 0) : 1 ≤ |(Algebra.norm ℚ (γ : E) : ℝ)| := by
  have h := Algebra.coe_norm_int γ
  have hne : Algebra.norm ℤ γ ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at h
    exact (Algebra.norm_ne_zero_iff.mpr (by exact_mod_cast hγ : (γ : E) ≠ 0)) h.symm
  rw [← h]
  have := Int.one_le_abs hne
  push_cast
  exact_mod_cast this

lemma sep (γ : 𝓞 E) (hγ : γ ≠ 0) : ∃ w : CP E, 1 ≤ ‖w.1.embedding (γ : E)‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  set w1 : CP E := ⟨w0, IsTotallyComplex.isComplex w0⟩
  have h := prod_norm (E := E) (γ : E)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w1)] at h
  have hle : ∏ w ∈ Finset.univ.erase w1, ‖w.1.embedding (γ : E)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => by positivity)
      (fun w _ => pow_le_one₀ (norm_nonneg _) (hcon w).le)
  have hlt : ‖w1.1.embedding (γ : E)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) (hcon w1) two_ne_zero
  have := one_le_abs_norm γ hγ
  rw [← h] at this
  nlinarith [mul_le_of_le_one_right (sq_nonneg ‖w1.1.embedding (γ : E)‖) hle]

theorem count (R : ℝ) (hR : 0 ≤ R) :
    {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E) := by
  set T := {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}
  have hT : T.Finite := by
    have h := Embeddings.finite_of_norm_le E ℂ R
    refine (h.preimage (Set.injOn_of_injective RingOfIntegers.coe_injective)).subset ?_
    intro α hα
    exact ⟨α.isIntegral_coe, hα⟩
  refine ⟨hT, ?_⟩
  let p : 𝓞 E → (CP E → ℂ) := fun α w => w.1.embedding (α : E)
  have hpinj : Function.Injective p := by
    intro α β h
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    have := congrFun h ⟨w0, IsTotallyComplex.isComplex w0⟩
    exact RingOfIntegers.coe_injective (w0.embedding.injective this)
  have hd : finrank ℝ (CP E → ℂ) = 2 * fdeg E := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, (card_CP (E := E)).1, mul_comm]
  have hcard : T.ncard = (hT.toFinset.image p).card := by
    rw [Finset.card_image_of_injective _ hpinj, Set.ncard_eq_toFinset_card _ hT]
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have : Nonempty (CP E) := ⟨⟨w0, IsTotallyComplex.isComplex w0⟩⟩
  rw [hcard, ← hd]
  refine pack volume _ R hR ?_ ?_
  · intro q hq
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hq
    rw [Set.Finite.mem_toFinset] at hα
    exact (pi_norm_le_iff_of_nonneg hR).mpr fun w => hα _
  · intro q hq q' hq' hne
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hq'
    have hαβ : α - β ≠ 0 := sub_ne_zero.mpr fun h => hne (by rw [h])
    obtain ⟨w, hw⟩ := sep (α - β) hαβ
    calc (1 : ℝ) ≤ ‖w.1.embedding ((α - β : 𝓞 E) : E)‖ := hw
      _ = ‖(p α - p β) w‖ := by simp [p]
      _ ≤ ‖p α - p β‖ := norm_le_pi_norm _ w

end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
end
