module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

section

open Matrix

namespace GlobalTheory

def imFormRight {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun w := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [star_add, mulVec_add, dotProduct_add]
  map_smul' r w := by
    simp [star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im]

def imFormLeft {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun z := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [add_dotProduct]
  map_smul' r z := by
    simp [smul_dotProduct, Complex.smul_im]

theorem herm_endo_matrix_rat : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by
  intro g n e H₁ H₂ hpos h1 h2 γ hγ
  classical
  set T := LinearMap.toMatrix e e (γ.restrictScalars ℝ) with hT
  let A₁ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₁ *ᵥ star (e l)).im
  let A₂ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₂ *ᵥ star (e l)).im

  have hγe : ∀ l, γ (e l) = ∑ m, T m l • e m := by
    intro l
    have := e.sum_repr (γ (e l))
    rw [← this]
    simp [hT, LinearMap.toMatrix_apply]

  have key : A₁ * T = A₂ := by
    ext k l
    rw [Matrix.mul_apply]
    show _ = (e k ⬝ᵥ H₂ *ᵥ star (e l)).im
    rw [hγ, hγe l]
    have := map_sum (imFormRight H₁ (e k)) (fun m : Fin n => T m l • e m) (Finset.univ : Finset (Fin n))
    simp only [map_smul, smul_eq_mul] at this
    change _ = imFormRight H₁ (e k) _
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]; rfl

  have hdet : A₁.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    set v := ∑ l, x l • e l with hv
    have hk : ∀ k, imFormRight H₁ (e k) v = 0 := by
      intro k
      have := congrFun hx k

      rw [hv, map_sum]
      simp only [map_smul, smul_eq_mul]
      simp only [mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]; rfl
    have hu : ∀ u, imFormLeft H₁ v u = 0 := by
      intro u

      rw [← e.sum_repr u, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [map_smul]
      have := hk k
      simp only [imFormRight, imFormLeft, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
      rw [this, smul_zero]
    have hre : (v ⬝ᵥ H₁ *ᵥ star v).re = 0 := by
      have := hu (Complex.I • v)
      simp only [imFormLeft, LinearMap.coe_mk, AddHom.coe_mk, smul_dotProduct, smul_eq_mul,
        Complex.mul_im, Complex.I_re, Complex.I_im] at this
      simpa using this
    have hv0 : v = 0 := by
      by_contra hne
      have := hpos v hne
      linarith
    apply hx0
    have : e.equivFun.symm x = 0 := by rw [Module.Basis.equivFun_symm_apply]; exact hv0
    exact e.equivFun.symm.injective (by rw [this, map_zero])

  choose m₁ hm₁ using h1
  choose m₂ hm₂ using h2
  let A₁q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₁ k l : ℚ)
  let A₂q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₂ k l : ℚ)
  have hA₁ : A₁q.map (Rat.castHom ℝ) = A₁ := by
    ext k l
    show ((m₁ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₁]
  have hA₂ : A₂q.map (Rat.castHom ℝ) = A₂ := by
    ext k l
    show ((m₂ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₂]
  have hdetq : IsUnit A₁q.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    have := (Rat.castHom ℝ).map_det A₁q
    rw [h0, map_zero] at this
    rw [← hA₁]
    exact this.symm
  have hdetR : IsUnit A₁.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨A₁q⁻¹ * A₂q, ?_⟩
  have h3 : A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = A₂ := by
    have := congrArg (fun M => M.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv_cancel_left A₁q A₂q hdetq)
    rw [Matrix.map_mul, hA₁, hA₂] at this
    exact this
  have h4 : (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = T := by
    calc (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)
        = A₁⁻¹ * (A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)) :=
          (Matrix.nonsing_inv_mul_cancel_left A₁ _ hdetR).symm
      _ = A₁⁻¹ * (A₁ * T) := by rw [h3, key]
      _ = T := Matrix.nonsing_inv_mul_cancel_left A₁ T hdetR
  simpa using h4

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

open Matrix

noncomputable def realDotC {g : ℕ} (u w : Fin g → ℂ) : ℝ :=
  ∑ k, ((u k).re * (w k).re + (u k).im * (w k).im)

lemma realDotC_comm {g : ℕ} (u w : Fin g → ℂ) : realDotC u w = realDotC w u := by
  unfold realDotC; refine Finset.sum_congr rfl (fun k _ => ?_); ring

lemma realDotC_sum_right {g m : ℕ} (u : Fin g → ℂ) (x : Fin m → ℝ) (μ : Fin m → Fin g → ℂ) :
    realDotC u (∑ i, x i • μ i) = ∑ i, x i * realDotC u (μ i) := by
  unfold realDotC
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.re_sum, Complex.im_sum, Complex.smul_re,
    Complex.smul_im, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring

lemma realDotC_self_eq_zero {g : ℕ} (u : Fin g → ℂ) (h : realDotC u u = 0) : u = 0 := by
  unfold realDotC at h
  have hn : ∀ k ∈ Finset.univ, 0 ≤ (u k).re * (u k).re + (u k).im * (u k).im :=
    fun k _ => by nlinarith [sq_nonneg (u k).re, sq_nonneg (u k).im]
  rw [Finset.sum_eq_zero_iff_of_nonneg hn] at h
  funext k
  have hk := h k (Finset.mem_univ _)
  apply Complex.ext <;> simp <;> nlinarith [sq_nonneg (u k).re, sq_nonneg (u k).im]

theorem continuousOn_coords_of_linearIndependent :
    ∀ (g m : ℕ) (U : Set ℂ) (μ : ℂ → Fin m → Fin g → ℂ) (v : ℂ → Fin g → ℂ) (c : ℂ → Fin m → ℝ),
      ContinuousOn μ U → ContinuousOn v U → (∀ s ∈ U, LinearIndependent ℝ (μ s)) →
      (∀ s ∈ U, v s = ∑ i, c s i • μ s i) → ContinuousOn c U := by
  intro g m U μ v c hμ hv hli hc
  rw [continuousOn_iff_continuous_restrict] at hμ hv ⊢
  let G : U → Matrix (Fin m) (Fin m) ℝ := fun s a b => realDotC (μ s a) (μ s b)
  let b : U → Fin m → ℝ := fun s a => realDotC (μ s a) (v s)
  have hdot : Continuous (fun p : (Fin g → ℂ) × (Fin g → ℂ) => realDotC p.1 p.2) := by
    unfold realDotC; fun_prop
  have hμa : ∀ a, Continuous (fun s : U => μ s a) := fun a => (continuous_apply a).comp hμ
  have hGc : Continuous G :=
    continuous_pi (fun a => continuous_pi (fun b' => hdot.comp ((hμa a).prodMk (hμa b'))))
  have hbc : Continuous b := continuous_pi (fun a => hdot.comp ((hμa a).prodMk hv))
  have hGc_eq : ∀ s : U, G s *ᵥ (c s) = b s := by
    intro s; funext a
    simp only [G, b, Matrix.mulVec, dotProduct]
    rw [hc s s.2, realDotC_sum_right]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
  have hdet : ∀ s : U, (G s).det ≠ 0 := by
    intro s hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    apply hx0
    have hw : ∑ i, x i • μ s i = 0 := by
      apply realDotC_self_eq_zero
      rw [realDotC_sum_right]
      have key : ∀ i, realDotC (μ s i) (∑ j, x j • μ s j) = (G s *ᵥ x) i := by
        intro i; rw [realDotC_sum_right]; simp only [G, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl (fun j _ => ?_); ring
      simp_rw [realDotC_comm _ (μ s _), key, hx]; simp
    funext i
    exact Fintype.linearIndependent_iff.mp (hli s s.2) x hw i
  have hceq : U.domRestrict c = fun s => ((G s).det)⁻¹ • ((G s).adjugate *ᵥ b s) := by
    funext s
    have h1 : c s = (G s)⁻¹ *ᵥ b s := by
      rw [← hGc_eq s, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s)), Matrix.one_mulVec]
    show c s = _
    rw [h1, Matrix.inv_def, Ring.inverse_eq_inv']
    ext a; simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  rw [hceq]
  exact (hGc.matrix_det.inv₀ hdet).smul (hGc.matrix_adjugate.matrix_mulVec hbc)

end GlobalTheory
end

section

open IsDedekindDomain NumberField
open scoped Classical

theorem GlobalTheory.continuousMultilinear_norm_le_basis_sum : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  intro E _ _ ι _ b j
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  set C := ‖(b.equivFunL : E →L[ℝ] (ι → ℝ))‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hcoord : ∀ (x : E) (c : ι), ‖b.repr x c‖ ≤ C * ‖x‖ := by
    intro x c
    have h1 : b.repr x c = (b.equivFunL : E →L[ℝ] (ι → ℝ)) x c := rfl
    rw [h1]
    exact (norm_le_pi_norm _ c).trans ((b.equivFunL : E →L[ℝ] (ι → ℝ)).le_opNorm x)
  refine ⟨C ^ j, pow_nonneg hC0 _, fun M => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound
  · exact mul_nonneg (pow_nonneg hC0 _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv : v = fun r => ∑ c, b.repr (v r) c • b c := funext fun r => (b.sum_repr (v r)).symm
  have key : M v = ∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r)) := by
    conv_lhs => rw [hv]

    rw [M.map_sum]
    refine Finset.sum_congr rfl fun cs _ => ?_
    exact M.map_smul_univ (fun r => b.repr (v r) (cs r)) (fun r => b (cs r))
  rw [key]
  calc ‖∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖
      ≤ ∑ cs : Fin j → ι, ‖(∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖ := norm_sum_le _ _
    _ ≤ ∑ cs : Fin j → ι, (C ^ j * ∏ r, ‖v r‖) * ‖M (fun r => b (cs r))‖ := by
      refine Finset.sum_le_sum fun cs _ => ?_
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => hcoord (v r) (cs r)
    _ = C ^ j * (∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖) * ∏ r, ‖v r‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cs _ => ?_
      ring
end

section

open Matrix

namespace GlobalTheory.HermGram

noncomputable def reForm {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ H *ᵥ star w).re)
    (by intro a b c; simp [add_dotProduct])
    (by intro c a b; simp [smul_dotProduct, Complex.smul_re])
    (by intro a b c; simp [star_add, mulVec_add, dotProduct_add])
    (by intro c a b
        have : star (c • b) = c • star b := by
          ext i; simp [Complex.conj_ofReal]
        rw [this, mulVec_smul, dotProduct_smul, Complex.smul_re])

theorem reForm_apply {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    reForm H z w = (z ⬝ᵥ H *ᵥ star w).re := rfl

theorem reForm_symm {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (z w : Fin g → ℂ) : reForm H z w = reForm H w z := by
  simp only [reForm_apply]
  have : star (z ⬝ᵥ H *ᵥ star w) = w ⬝ᵥ H *ᵥ star z := by
    simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.apply i j]; ring
  rw [← this]; simp

theorem gram_posDef {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) :
    (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext k l
    simp only [conjTranspose_apply, of_apply, star_trivial]
    exact reForm_symm hH (e l) (e k)
  · intro x hx
    set v : Fin g → ℂ := ∑ k, x k • e k with hvdef
    have hv : v ≠ 0 := by
      intro h0
      apply hx
      apply e.equivFun.symm.injective
      rw [map_zero, Module.Basis.equivFun_symm_apply]
      exact h0
    have key : star x ⬝ᵥ (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re) *ᵥ x
        = reForm H v v := by
      rw [hvdef]
      change star x ⬝ᵥ (Matrix.of fun k l => reForm H (e k) (e l)) *ᵥ x = _

      simp only [star_trivial, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, dotProduct, mulVec, of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [reForm_symm hH (e l) (e k)]; ring
    rw [key, reForm_apply]
    exact hpos v hv

theorem gram_posDef_pair (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (p₁ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re)
    (p₂ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hγ : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) :
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  refine ⟨gram_posDef e h₁ p₁, ?_⟩
  have hG : (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ) =
      Matrix.of fun k l => (e k ⬝ᵥ H₂.mulVec (star (e l))).re := by
    ext k l
    rw [of_apply, hγ, Matrix.mul_apply]
    have hs : γ (e l) = ∑ m, e.repr (γ (e l)) m • e m := (e.sum_repr _).symm
    have : (e k ⬝ᵥ H₁.mulVec (star (γ (e l)))).re = reForm H₁ (e k) (γ (e l)) := rfl
    rw [this, hs]

    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.toMatrix_apply, of_apply,
    LinearMap.restrictScalars_apply, reForm_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hG]
  exact gram_posDef e h₂ p₂

end GlobalTheory.HermGram
end

section

open MeasureTheory

namespace GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)


omit [μ.IsMulLeftInvariant] [Countable Γ] in
theorem isFundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) ⁻¹' 𝓕) μ :=
  h𝓕.preimage_of_equiv (measurePreserving_mul_right μ y).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g h => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])

omit [μ.IsMulLeftInvariant] [Countable Γ] [μ.IsMulRightInvariant] [TopologicalSpace H]
  [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] in
theorem preimage_preimage_mul (y : H) :
    (fun h => h * y) ⁻¹' ((fun h => h * y⁻¹) ⁻¹' 𝓕) = 𝓕 := by
  ext h; simp

theorem setIntegral_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  have h1 := (measurePreserving_mul_right μ y).setIntegral_preimage_emb
    (measurableEmbedding_mulRight y) u ((fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  rw [h1]
  exact (isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).setIntegral_eq h𝓕
    (fun g h => hu g g.2 h)

theorem integrableOn_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  have h1 := (measurePreserving_mul_right μ y).integrableOn_comp_preimage
    (measurableEmbedding_mulRight y) (f := u) (s := (fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  refine h1.2 ?_
  exact ((isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).integrableOn_iff h𝓕
    (fun g h => hu g g.2 h)).2 hi


omit [Group H] [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
theorem integrableOn_star_mul (F F' : H → ℂ) (hF : Continuous F) (hF' : Continuous F')
    (h1 : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ)
    (h2 : IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ) :
    IntegrableOn (fun h => star (F h) * F' h) 𝓕 μ := by
  refine Integrable.mono' (h1.norm.add h2.norm)
    (hF.star.mul hF').aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  simp only [Pi.add_apply, norm_mul, norm_star]
  nlinarith [sq_nonneg (‖F h‖ - ‖F' h‖), mul_nonneg (norm_nonneg (F h)) (norm_nonneg (F' h))]

end GlobalTheory.DoubleCosetAdjoint


open GlobalTheory.DoubleCosetAdjoint in
theorem GlobalTheory.doubleCosetSum_adjoint : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  intro H _ _ _ _ _ μ _ _ Γ K _ 𝓕 x A A' F F' h𝓕 hA hA' hc cF cF' lF lF' rF rF' iF iF'
  set u : H → ℂ := fun h => star (F (h * x)) * F' h with hu
  have lu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h := by
    intro γ hγ h
    simp only [hu, mul_assoc, lF γ hγ, lF' γ hγ]
  have iu : IntegrableOn u 𝓕 μ := by
    refine integrableOn_star_mul μ 𝓕 (fun h => F (h * x)) F'
      (cF.comp (continuous_mul_const x)) cF' ?_ iF'
    exact integrableOn_mul_right μ Γ 𝓕 h𝓕 (fun h => star (F h) * F h)
      (fun γ hγ h => by simp only [lF γ hγ]) x iF
  have eA : ∀ a ∈ A, ∃ y, ∀ h, star (F (h * a)) * F' h = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF k₂ hk₂, rF' k₁ hk₁]
  have eA' : ∀ a ∈ A', ∃ y, ∀ h, star (F h) * F' (h * a) = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF' k₂ hk₂, inv_mul_cancel_right, rF k₁ hk₁]
  have key : ∀ (B : Finset H) (t : H → H → ℂ), (∀ a ∈ B, ∃ y, ∀ h, t a h = u (h * y)) →
      ∫ h in 𝓕, ∑ a ∈ B, t a h ∂μ = B.card • ∫ h in 𝓕, u h ∂μ := by
    intro B t ht
    rw [MeasureTheory.integral_finsetSum, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨y, hy⟩ := ht a ha
      simp only [hy]
      exact setIntegral_mul_right μ Γ 𝓕 h𝓕 u lu y
    · intro a ha
      obtain ⟨y, hy⟩ := ht a ha
      have : t a = fun h => u (h * y) := funext hy
      rw [this]
      exact integrableOn_mul_right μ Γ 𝓕 h𝓕 u lu y iu
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [key A (fun a h => star (F (h * a)) * F' h) eA,
    key A' (fun a h => star (F h) * F' (h * a)) eA', hc]
end
