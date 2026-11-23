module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
public import Lemmata.GeneralBFactBisForm.Imports
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def Am (u : Fin 2 → Fin r → E) (τ : X.Ψ) : Matrix (Fin r) (Fin 2) ℂ :=
  Matrix.of fun a i => emb τ.1 (u i) a

noncomputable def Cm (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    Matrix (Fin 2) (Fin r) ℂ :=
  Matrix.of fun i j => -(I * X.c τ) * ∑ k, b τ i k * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)

theorem zmat_eq (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ = 1 + X.Am u τ * X.Cm u b τ := by
  ext a j
  simp only [Data.zmat, Data.Am, Data.Cm, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]
  ring

theorem Cm_add (u : Fin 2 → Fin r → E) (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.Cm u (b + b') τ = X.Cm u b τ + X.Cm u b' τ := by
  ext i j
  simp only [Data.Cm, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma Cm_mulVec_apply (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ)
    (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  simp only [Matrix.mulVec, dotProduct, Data.Cm, Matrix.of_apply, hermC, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem Cm_mul_Am (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : X.Cm u b τ * X.Am u τ = 0 := by
  ext i i'
  have e : (X.Cm u b τ * X.Am u τ) i i' = (X.Cm u b τ *ᵥ emb τ.1 (u i')) i := rfl
  rw [e, Cm_mulVec_apply X u b τ, Matrix.zero_apply]
  simp only [hermC_emb, hu, map_zero, mul_zero, Finset.sum_const_zero]

theorem zmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ * X.zmat u b' τ = X.zmat u (b + b') τ := by
  have h := X.Cm_mul_Am u hu b τ
  rw [X.zmat_eq u b τ, X.zmat_eq u b' τ, X.zmat_eq u (b + b') τ, X.Cm_add]
  calc (1 + X.Am u τ * X.Cm u b τ) * (1 + X.Am u τ * X.Cm u b' τ)
      = 1 + X.Am u τ * X.Cm u b τ + X.Am u τ * X.Cm u b' τ +
          X.Am u τ * (X.Cm u b τ * X.Am u τ) * X.Cm u b' τ := by
        simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
        abel
    _ = 1 + X.Am u τ * (X.Cm u b τ + X.Cm u b' τ) := by
        rw [h, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_add, add_assoc]

theorem zmat_det (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : (X.zmat u b τ).det = 1 := by
  rw [X.zmat_eq, Matrix.det_one_add_mul_comm, X.Cm_mul_Am u hu, add_zero, Matrix.det_one]

theorem Am_mulVec (u : Fin 2 → Fin r → E) (τ : X.Ψ) (y : Fin 2 → ℂ) :
    X.Am u τ *ᵥ y = ∑ i, y i • emb τ.1 (u i) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Data.Am, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Cm_mulVec (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  exact Cm_mulVec_apply X u b τ v i

theorem zmat_unitary (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.zmat u b τ *ᵥ v) (X.zmat u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by
  have hee : ∀ i k, hermC τ.1 X.Gm (emb τ.1 (u i)) (emb τ.1 (u k)) = 0 := fun i k => by
    rw [hermC_emb, hu, map_zero]
  have hb' : ∀ i k, conj (b τ i k) = b τ k i := fun i k => (hb τ i k).symm
  have hcw : ∀ k, conj (hermC τ.1 X.Gm w (emb τ.1 (u k))) = hermC τ.1 X.Gm (emb τ.1 (u k)) w :=
    fun k => hermC_conj τ.1 X.Gm_herm _ _
  rw [X.zmat_eq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, X.Am_mulVec, X.Am_mulVec]
  simp only [Fin.sum_univ_two, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hee,
    X.Cm_mulVec, map_mul, map_add, map_neg, hb', hcw, Complex.conj_I, Complex.conj_ofReal, mul_zero, add_zero]
  ring

theorem mat_Zb (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl

theorem Zb_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) :
    X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x := by
  funext τ
  show X.zmat u b τ * mat (X.Zb u b' x) τ = X.zmat u (b + b') τ * mat x τ
  rw [X.mat_Zb, ← Matrix.mul_assoc, X.zmat_mul u hu]

private lemma col_mul_eq_mulVec_col (M N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (M * N) a = M *ᵥ col N a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.Zb u b x) τ) = gram τ.1 X.Gm (mat x τ) := by
  rw [X.mat_Zb]
  ext a a'
  simp only [gram, Matrix.of_apply, col_mul_eq_mulVec_col]
  exact X.zmat_unitary u hu b hb τ _ _

theorem dmin_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
  unfold dmin
  rw [X.gram_Zb u hu b hb x τ]

theorem Zb_dom (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.Zb u b x ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [X.mat_Zb, Matrix.det_mul, X.zmat_det u hu, one_mul]
    exact (hx τ).1
  · rw [X.dmin_Zb u hu b hb]
    exact (hx τ).2 i

theorem nfac_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    X.nfac la (X.Zb u b x) = X.nfac la x := by
  simp only [Data.nfac, X.dmin_Zb u hu b hb]

theorem flowV_uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flowV (X.uvec u a) s x = X.Zb u (fun τ i k => s τ * a τ i * conj (a τ k)) x := by
  funext τ
  show X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ =
    X.zmat u (fun τ i k => s τ * a τ i * conj (a τ k)) τ * mat x τ
  congr 1
  ext p q
  have hk : ∀ k, ∑ l, τ.1 (X.Gm q l) * (conj (a τ k) * conj (emb τ.1 (u k) l)) =
      conj (a τ k) * ∑ l, τ.1 (X.Gm q l) * conj (emb τ.1 (u k) l) := fun k => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Data.flowMatV, Data.zmat, Matrix.of_apply, Data.uvec, Fin.sum_univ_two, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, hk]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology

noncomputable section

section Cauchy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma norm_fderiv_le {U : Set F} (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U)
    {y : F} {R C : ℝ} (hR : 0 < R) (hball : closedBall y R ⊆ U)
    (hC : ∀ z ∈ closedBall y R, ‖G z‖ ≤ C) : ‖fderiv ℂ G y‖ ≤ C / R := by
  first | exact Bl.general_b_fact_bis_form.goal1 .. | (apply Bl.general_b_fact_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_form.goal1 <;> assumption)

end Cauchy

section Param

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ}

theorem diffOn_param {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKm : MeasurableSet K)
    (A : (Fin n → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t ∈ K, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (Fin n → ℝ) → ℂ) (he : Continuous e) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  have hcA : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  set K0 := (fun t => A t x0) '' K with hK0def
  have hK0 : IsCompact K0 := hK.image (hcA x0)
  have hK0U : K0 ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hAU t ht x0 hx0
  obtain ⟨δ, hδ, hδU⟩ := hK0.exists_cthickening_subset_open hU hK0U
  have hK1 : IsCompact (cthickening δ K0) := hK0.cthickening
  obtain ⟨C, hC⟩ := hK1.exists_bound_of_continuousOn (hG.continuousOn.mono hδU)
  obtain ⟨Am, hAm⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨Me, hMe⟩ := hK.exists_bound_of_continuousOn he.continuousOn
  set A1 := max Am 1 with hA1def
  have hA1 : 0 < A1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := δ / 2 / A1 with hεdef
  have hε : 0 < ε := by positivity
  have hnear : ∀ t ∈ K, ∀ x ∈ ball x0 ε, closedBall (A t x) (δ / 2) ⊆ cthickening δ K0 := by
    intro t ht x hx z hz
    have hx' : ‖x - x0‖ < ε := by rw [← dist_eq_norm]; exact hx
    have h1 : dist (A t x) (A t x0) ≤ δ / 2 := by
      rw [dist_eq_norm, ← map_sub]
      calc ‖A t (x - x0)‖ ≤ ‖A t‖ * ‖x - x0‖ := (A t).le_opNorm _
        _ ≤ A1 * ε := mul_le_mul (le_trans (hAm t ht) (le_max_left _ _)) hx'.le (norm_nonneg _) hA1.le
        _ = δ / 2 := by rw [hεdef]; field_simp
    have h2 : dist z (A t x0) ≤ δ := by
      linarith [dist_triangle z (A t x) (A t x0), mem_closedBall.1 hz]
    exact mem_cthickening_of_dist_le z (A t x0) δ K0 ⟨t, ht, rfl⟩ h2
  have hin : ∀ t ∈ K, ∀ x ∈ ball x0 ε, A t x ∈ U := fun t ht x hx =>
    hδU (hnear t ht x hx (mem_closedBall_self (by positivity)))
  have hfd : ∀ t ∈ K, ∀ x ∈ ball x0 ε, ‖fderiv ℂ G (A t x)‖ ≤ C / (δ / 2) := fun t ht x hx =>
    norm_fderiv_le hU hG (by positivity) ((hnear t ht x hx).trans hδU)
      (fun z hz => hC z (hnear t ht x hx hz))
  have hball : ball x0 ε ∈ 𝓝 x0 := ball_mem_nhds x0 hε
  have hcont : ∀ x ∈ ball x0 ε, ContinuousOn (fun t => G (A t x) * e t) K := fun x hx =>
    (hG.continuousOn.comp (hcA x).continuousOn (fun t ht => hin t ht x hx)).mul he.continuousOn
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have m1 : Measurable fun t => fderiv ℂ G (A t x0) := (measurable_fderiv ℂ G).comp (hcA x0).measurable
  have m2 : Measurable fun t => (fderiv ℂ G (A t x0)).comp (A t) :=
    (isBoundedBilinearMap_comp.continuous.measurable).comp (m1.prodMk hA.measurable)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t)
    (F' := fun x t => e t • (fderiv ℂ G (A t x)).comp (A t))
    (bound := fun _ => Me * (C / (δ / 2) * A1)) hball
    (by filter_upwards [hball] with x hx; exact (hcont x hx).aestronglyMeasurable hKm)
    ((hcont x0 (mem_ball_self hε)).integrableOn_compact hK)
    ((he.measurable.smul m2).aestronglyMeasurable)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      calc ‖e t • (fderiv ℂ G (A t x)).comp (A t)‖
          = ‖e t‖ * ‖(fderiv ℂ G (A t x)).comp (A t)‖ := norm_smul _ _
        _ ≤ Me * (C / (δ / 2) * A1) := by
          refine mul_le_mul (hMe t ht) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hMe t ht))
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hfd t ht x hx)
            (le_trans (hAm t ht) (le_max_left _ _)) (norm_nonneg _)
            (le_trans (norm_nonneg _) (hfd t ht x hx)))))
    (integrable_const _)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      have h1 : HasFDerivAt G (fderiv ℂ G (A t x)) (A t x) :=
        (hG.differentiableAt (hU.mem_nhds (hin t ht x hx))).hasFDerivAt
      exact (h1.comp x (A t).hasFDerivAt).mul_const (e t)))
  exact key.differentiableAt.differentiableWithinAt

end Param

section Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

lemma cont_gram (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

lemma isOpen_dom : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x; simp [Data.dom, GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det
      continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      ((cont_gram X τ).matrix_submatrix _ _).matrix_det))

def ZbL (b : X.Ψ → Fin 2 → Fin 2 → ℂ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.Zb u b
      map_add' x y := by
        funext τ
        show X.zmat u b τ * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.zmat u b τ * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }

lemma cont_Zb {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) (y : Frame X.Ψ r) : Continuous fun t => X.Zb u (B t) y := by
  have hB' : ∀ τ i k, Continuous fun t => B t τ i k := fun τ i k => by fun_prop
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  simp only [Data.Zb, Data.zmat, Matrix.mul_apply, Matrix.of_apply, mat]
  fun_prop

lemma cont_ZbL {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) : Continuous fun t => ZbL X u (B t) :=
  continuous_clm_apply.2 fun y => cont_Zb X u hB y

end Dom

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

section onetau

variable (ξ : Fin r → E) (τ : X.Ψ)

private theorem flowMat_mulVec' (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v - (I * X.c τ * s * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  ext a
  simp only [Matrix.mulVec, dotProduct, flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem hermC_sub_const_smul_right (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (w v e : Fin r → ℂ) (k : ℂ) :
    hermC σ G w (v - k • e) = hermC σ G w v - conj k * hermC σ G w e := by
  simp only [hermC, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
  ring

lemma flow_fix (s : ℂ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (emb τ.1 ξ) = 0) :
    Matrix.mulVec (X.flowMat ξ τ s) v = v := by
  rw [flowMat_mulVec', hv, mul_zero, zero_smul, sub_zero]

lemma hC_right_flow (s : ℂ) (y v : Fin r → ℂ) (hy : hermC τ.1 X.Gm y (emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm y (Matrix.mulVec (X.flowMat ξ τ s) v) = hermC τ.1 X.Gm y v := by
  rw [flowMat_mulVec', hermC_sub_const_smul_right, hy, mul_zero, sub_zero]

lemma col_flow (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (a : Fin r) :
    col (mat (X.flow ξ s x) τ) a = Matrix.mulVec (X.flowMat ξ τ (s τ)) (col (mat x τ) a) := by
  ext k
  rfl

lemma mulVec_lin (M : Matrix (Fin r) (Fin r) ℂ) {n : ℕ} (β : Fin n → ℂ) (v : Fin n → Fin r → ℂ) :
    Matrix.mulVec M (∑ a, β a • v a) = ∑ a, β a • Matrix.mulVec M (v a) := by
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma ppos_flow {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom)
    (u : Fin r → ℂ) (hu : hermC τ.1 X.Gm u (emb τ.1 ξ) = 0)
    (hp : hermC τ.1 X.Gm (X.ppos x τ u) (emb τ.1 ξ) = 0) :
    X.ppos (X.flow ξ s x) τ u = X.ppos x τ u := by
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a with hα
  have hpx : X.ppos x τ u = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hT : ∑ a, α a • col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a) = X.ppos x τ u := by
    simp only [col_flow]
    rw [← mulVec_lin, ← hpx, flow_fix X ξ τ _ _ hp]
  rw [← hT]
  apply ppos_eq_of X (X.flow ξ s x) τ (gramPos_det_ne X hxs τ) u α
  intro b
  rw [hT, col_flow, hC_right_flow]
  · exact ppos_orth X x τ (gramPos_det_ne X hx τ) u b
  · rw [hC_sub_left, hu, hp, sub_zero]

end onetau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem orthogonal_lattice_decomposition : ProjectionAlongComplement (E := E) := by
  intro r X ξ hξ x hx u hu
  obtain ⟨-, hiso, hne⟩ := hξ
  have key : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.ucomp x ξ u τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.Jz x (X.ucomp x ξ u) τ) (Data.emb τ.1 ξ) = 0 := by
    intro τ
    set e := Data.emb τ.1 ξ with he
    have he0 : e ≠ 0 := emb_ne_zero τ.1 hne
    have hee : hermC τ.1 X.Gm e e = 0 := by rw [he, hermC_emb, hiso, map_zero]
    have hη : X.Hf x τ e e ≠ 0 := fun h => by
      have := X.Hf_iso_pos hx τ he0 hee
      rw [h] at this; simp at this
    have hu' : X.ucomp x ξ u τ = u τ - (X.Hf x τ (u τ) e / X.Hf x τ e e) • e := rfl
    refine ⟨?_, ?_⟩
    · rw [hu', hermC_sub_left, hermC_smul_left, hee, mul_zero, sub_zero]
      exact hu τ
    · rw [Data.Jz_apply, hu', hermC_smul_left, Data.jp_sub, Data.jp_smul, hermC_sub_left,
        hermC_smul_left, ← Data.Hf_eq_jp, ← Data.Hf_eq_jp, div_mul_cancel₀ _ hη, sub_self, mul_zero]
  exact ⟨fun τ => (key τ).1, fun τ => (key τ).2⟩

end ReciprocityTheory.ChartRestriction.G.FD
end
